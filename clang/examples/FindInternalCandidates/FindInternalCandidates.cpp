//===- FindInternalCandidates.cpp ----------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Clang plugin which locates candidate private methods which could be
// internalized in implementation file. Such methods must obey certain constraints
// which allow us to guarantee that they are only referenced in implementation file.
//
//===----------------------------------------------------------------------===//

#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"

#include <vector>
#include <set>

using namespace clang;

#define PLUGIN_NAME "FindInternalCandidates"

namespace {

int V;

namespace {

std::string getDeclName(const NamedDecl *D) {
  std::string S;
  llvm::raw_string_ostream OS(S);
  D->printQualifiedName(OS);
  return S;
}

using CallGraph = std::map<const CXXMethodDecl *, std::set<const CXXMethodDecl *>>;

CallGraph buildCallGraph(const CXXRecordDecl *D) {
  struct CallVisitor : public RecursiveASTVisitor<CallVisitor> {
    std::set<const CXXMethodDecl *> &Callees;
    CallVisitor(std::set<const CXXMethodDecl *> &Callees) : Callees(Callees) {}
    bool VisitCXXMemberCallExpr(CXXMemberCallExpr *E) {
      Callees.insert(E->getMethodDecl()->getCanonicalDecl());
      return true;
    }
    bool VisitCallExpr(CallExpr *E) {
      // Calls to static methods are represented with CallExpr's
      if (auto *D = dyn_cast_or_null<CXXMethodDecl>(E->getCalleeDecl()))
        Callees.insert(D->getCanonicalDecl());
      return true;
    }
  };

  CallGraph CG;
  for (auto *M : D->methods()) {
    if (M->isDeleted())
      continue;
    CallVisitor V(CG[M]);
    V.TraverseStmt(M->getBody());
  }

  if (V > 1) {
    auto ClassName = getDeclName(D);
    llvm::errs() << "Call graph for class " << ClassName << ":\n";
    for (auto &[Caller, Callees] : CG) {
      llvm::errs() << "  " << getDeclName(Caller) << "\n";
      for (auto *Callee : Callees)
        llvm::errs() << "    " << getDeclName(Callee) << "\n";
    }
  }

  return CG;
}

class FindInternalCandidatesConsumer : public ASTConsumer {
  void CollectInternalMethods(const CXXRecordDecl *D) {
    // Do not try to optimize std::

    if (D->isInStdNamespace())
      return;

    // No need to internalize classes from anon. namespaces

    if (D->isInAnonymousNamespace())
      return;

    // Skip fw decls

    if (!D->hasDefinition())
      return;

    auto ClassName = getDeclName(D);
    if (V > 1)
      llvm::errs() << "Analyzing class " << ClassName << "\n";

    // Skip classes that have friends
    // because they can call private methods outside of implementation file

    if (D->hasFriends()) {
      if (V > 1)
        llvm::errs() << "Skipping: friendly\n";
      return;
    }

    // Skip templates because their private methods have vague linkage

    if (D->isTemplated()) {
      if (V > 1)
        llvm::errs() << "Skipping: template\n";
      return;
    }

    // Skip template methods
    // TODO: can they be scanned for calls too?

    for (auto *DD : D->decls()) {
      if (isa<FunctionTemplateDecl>(DD)) {
        if (V > 1)
          llvm::errs() << "Skipping: template method\n";
        return;
      }
    }

    // Skip incomplete class definitions

    std::vector<const CXXMethodDecl *> Methods;
    for (auto *M : D->methods()) {
      if (M->isDeleted())
        continue;
      if (!M->getBody()) {
        if (V > 1) {
          llvm::errs() << "Skipping: undefined method " << getDeclName(M) << "\n";
        }
        return;
      }
      Methods.push_back(M);
    }

    // Collect candidates for internalization

    std::vector<const CXXMethodDecl *> Candidates;
    for (auto *M : Methods) {
      if (M->getAccess() == AS_private
          // FIXME: can we remove this?
          && !M->hasInlineBody()
          // Vtables may be emitted outside of class definition
          // TODO: can we do a precise check for this?
          && !M->isVirtual())
        Candidates.push_back(M->getCanonicalDecl());
    }

    if (Candidates.empty()) {
      if (V > 1)
        llvm::errs() << "Skipping: no candidate privates\n";
      return;
    }

    if (V > 1) {
      llvm::errs() << "Candidates for internalization:\n";
      for (auto *M : Candidates)
        llvm::errs() << "  " << getDeclName(M) << "\n";
    }

    // Collect non-private inline methods of class

    std::vector<const CXXMethodDecl *> InlineNonPrivates;
    for (auto *M : Methods) {
      // Only def may be marked as inlined, see MaybeTrackCord in abseil
      if (M->getAccess() != AS_private && (M->hasInlineBody() || M->getDefinition()->isInlined()))
        InlineNonPrivates.push_back(M->getCanonicalDecl());
    }

    if (V > 1) {
      llvm::errs() << "Non-private inline methods:\n";
      for (auto *M : InlineNonPrivates) {
        llvm::errs() << "  " << getDeclName(M) << "\n";
//        M->getBody()->dump();
      }
    }

    // Collect private methods which are reachable from other modules
    // i.e. callable through non-private inline methods
    //
    // TODO: do this more efficiently

    auto CG = buildCallGraph(D);

    std::set<const CXXMethodDecl *> ExternallyInlinable(InlineNonPrivates.begin(), InlineNonPrivates.end());

    bool Changed;
    do {
      auto ExternallyInlinableNew = ExternallyInlinable;

      for (auto *Caller : ExternallyInlinable) {
        for (auto *Callee : CG[Caller]) {
          if (Callee->hasInlineBody())
            ExternallyInlinableNew.insert(Callee);
        }
      }

      Changed = ExternallyInlinableNew != ExternallyInlinable;
      ExternallyInlinable = ExternallyInlinableNew;
    } while (Changed);

    if (V > 1) {
      llvm::errs() << "Externally inlinable:\n";
      for (auto *D : ExternallyInlinable)
        llvm::errs() << "  " << getDeclName(D) << "\n";
    }

    std::set<const CXXMethodDecl *> ExternallyUnreachablePrivates(Candidates.begin(), Candidates.end());
    for (auto *Caller : ExternallyInlinable) {
      for (auto *Callee : CG[Caller])
        ExternallyUnreachablePrivates.erase(Callee);
    }

    // Store results

    if (ExternallyUnreachablePrivates.empty())
      return;

    if (V) {
      llvm::errs() << "Internalizable private methods for class " << ClassName
        << " (" << ExternallyUnreachablePrivates.size() << "/" << Candidates.size() << "):\n";
      for (auto *D : ExternallyUnreachablePrivates) {
        auto MangledName = mangle(D);
        llvm::errs() << "  " << getDeclName(D) << " (" << MangledName << ")\n";
      }
    }

    // TODO
  }

public:
  void HandleTranslationUnit(ASTContext& Ctx) override {
    struct Visitor : public RecursiveASTVisitor<Visitor> {
      std::vector<const CXXRecordDecl *> Classes;
      Visitor() {}
      bool VisitCXXRecordDecl(CXXRecordDecl *FD) {
        Classes.push_back(FD);
        return true;
      }
    } V;
    V.TraverseDecl(Ctx.getTranslationUnitDecl());
    for (auto *FD : V.Classes)
      CollectInternalMethods(FD);
  }
};

class FindInternalCandidatesAction : public PluginASTAction {
public:
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                 llvm::StringRef) override {
    return std::make_unique<FindInternalCandidatesConsumer>();
  }

  bool ParseArgs(const CompilerInstance &CI,
                 const std::vector<std::string> &Args) override {
    for (unsigned I = 0, E = Args.size(); I != E; ++I) {
      // Example error handling.
      if (Args[I] == "verbose") {
        ++V;
      } else {
        llvm::errs() << PLUGIN_NAME << ": unknown argument: " << Args[I] << "\n";
        return false;
      }
    }

    return true;
  }

  PluginASTAction::ActionType getActionType() override {
    return AddBeforeMainAction;
  }
};

}

FrontendPluginRegistry::Add<FindInternalCandidatesAction>
X("find_internal_candidates", "find candidates for internalisation");

} // anon namespace
