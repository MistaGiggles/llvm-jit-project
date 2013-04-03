/*
 * Copyright (C) 2009 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
 #define __STDC_LIMIT_MACROS
 #define __STDC_CONSTANT_MACROS
#include <sstream>

#include "Dalvik.h"
#include "libdex/DexOpcodes.h"
#include "libdex/DexCatch.h"
#include "interp/Jit.h"
#include "CompilerInternals.h"
#include "Dataflow.h"
 //#include "compiler/codegen/arm/ArmLIR.h"

#include "llvm/LLVMContext.h"
#include "llvm/Module.h"
#include "llvm/Constants.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Instructions.h"
#include "llvm/ExecutionEngine/GenericValue.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/IRBuilder.h"


#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/JIT.h"
#include "llvm/ExecutionEngine/Interpreter.h"
#include "llvm/ExecutionEngine/JIT.h"
#include "llvm/ExecutionEngine/JITEventListener.h"
#include "llvm/ExecutionEngine/JITMemoryManager.h"
#include "llvm/Support/MemoryBuffer.h"



// 
#include "llvm/LLVMContext.h"
#include "llvm/Module.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Constants.h"
#include "llvm/GlobalVariable.h"
#include "llvm/Function.h"
#include "llvm/CallingConv.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instructions.h"
#include "llvm/InlineAsm.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/Verifier.h"
#include "llvm/Assembly/PrintModulePass.h"


 #include "llvm/LLVMContext.h"
#include "llvm/Module.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Constants.h"
#include "llvm/GlobalVariable.h"
#include "llvm/Function.h"
#include "llvm/CallingConv.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instructions.h"
#include "llvm/InlineAsm.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/Verifier.h"
#include "llvm/Assembly/PrintModulePass.h"
#include "llvm/LinkAllPasses.h"

#include "llvm/CodeGen/MachineCodeInfo.h"


extern "C" void dvmJitCalleeSave(double *saveArea);
extern "C" void dvmJitCalleeRestore(double *saveArea);


int opcodecount[256] = {};

//#include "llvmjit/llvmjit.h"

static inline bool contentIsInsn(const u2 *codePtr) {
    u2 instr = *codePtr;
    Opcode opcode = (Opcode)(instr & 0xff);

    /*
     * Since the low 8-bit in metadata may look like OP_NOP, we need to check
     * both the low and whole sub-word to determine whether it is code or data.
     */
    return (opcode != OP_NOP || instr == 0);
}

/*
 * Parse an instruction, return the length of the instruction
 */
static inline int parseInsn(const u2 *codePtr, DecodedInstruction *decInsn,
                            bool printMe)
{
    // Don't parse instruction data
    if (!contentIsInsn(codePtr)) {
        return 0;
    }

    u2 instr = *codePtr;
    Opcode opcode = dexOpcodeFromCodeUnit(instr);

    dexDecodeInstruction(codePtr, decInsn);
    if (printMe) {
        char *decodedString = dvmCompilerGetDalvikDisassembly(decInsn, NULL);
        ALOGD("%p: %#06x %s", codePtr, opcode, decodedString);
    }
    return dexGetWidthFromOpcode(opcode);
}

#define UNKNOWN_TARGET 0xffffffff

/*
 * Identify block-ending instructions and collect supplemental information
 * regarding the following instructions.
 */
static inline bool findBlockBoundary(const Method *caller, MIR *insn,
                                     unsigned int curOffset,
                                     unsigned int *target, bool *isInvoke,
                                     const Method **callee)
{
    switch (insn->dalvikInsn.opcode) {
        /* Target is not compile-time constant */
        case OP_RETURN_VOID:
        case OP_RETURN:
        case OP_RETURN_WIDE:
        case OP_RETURN_OBJECT:
        case OP_THROW:
          *target = UNKNOWN_TARGET;
          break;
        case OP_INVOKE_VIRTUAL:
        case OP_INVOKE_VIRTUAL_RANGE:
        case OP_INVOKE_INTERFACE:
        case OP_INVOKE_INTERFACE_RANGE:
        case OP_INVOKE_VIRTUAL_QUICK:
        case OP_INVOKE_VIRTUAL_QUICK_RANGE:
            *isInvoke = true;
            break;
        case OP_INVOKE_SUPER:
        case OP_INVOKE_SUPER_RANGE: {
            int mIndex = caller->clazz->pDvmDex->
                pResMethods[insn->dalvikInsn.vB]->methodIndex;
            const Method *calleeMethod =
                caller->clazz->super->vtable[mIndex];

            if (calleeMethod && !dvmIsNativeMethod(calleeMethod)) {
                *target = (unsigned int) calleeMethod->insns;
            }
            *isInvoke = true;
            *callee = calleeMethod;
            break;
        }
        case OP_INVOKE_STATIC:
        case OP_INVOKE_STATIC_RANGE: {
            const Method *calleeMethod =
                caller->clazz->pDvmDex->pResMethods[insn->dalvikInsn.vB];

            if (calleeMethod && !dvmIsNativeMethod(calleeMethod)) {
                *target = (unsigned int) calleeMethod->insns;
            }
            *isInvoke = true;
            *callee = calleeMethod;
            break;
        }
        case OP_INVOKE_SUPER_QUICK:
        case OP_INVOKE_SUPER_QUICK_RANGE: {
            const Method *calleeMethod =
                caller->clazz->super->vtable[insn->dalvikInsn.vB];

            if (calleeMethod && !dvmIsNativeMethod(calleeMethod)) {
                *target = (unsigned int) calleeMethod->insns;
            }
            *isInvoke = true;
            *callee = calleeMethod;
            break;
        }
        case OP_INVOKE_DIRECT:
        case OP_INVOKE_DIRECT_RANGE: {
            const Method *calleeMethod =
                caller->clazz->pDvmDex->pResMethods[insn->dalvikInsn.vB];
            if (calleeMethod && !dvmIsNativeMethod(calleeMethod)) {
                *target = (unsigned int) calleeMethod->insns;
            }
            *isInvoke = true;
            *callee = calleeMethod;
            break;
        }
        case OP_GOTO:
        case OP_GOTO_16:
        case OP_GOTO_32:
            *target = curOffset + (int) insn->dalvikInsn.vA;
            break;

        case OP_IF_EQ:
        case OP_IF_NE:
        case OP_IF_LT:
        case OP_IF_GE:
        case OP_IF_GT:
        case OP_IF_LE:
            *target = curOffset + (int) insn->dalvikInsn.vC;
            break;

        case OP_IF_EQZ:
        case OP_IF_NEZ:
        case OP_IF_LTZ:
        case OP_IF_GEZ:
        case OP_IF_GTZ:
        case OP_IF_LEZ:
            *target = curOffset + (int) insn->dalvikInsn.vB;
            break;

        default:
            return false;
    }
    return true;
}

static inline bool isGoto(MIR *insn)
{
    switch (insn->dalvikInsn.opcode) {
        case OP_GOTO:
        case OP_GOTO_16:
        case OP_GOTO_32:
            return true;
        default:
            return false;
    }
}

/*
 * Identify unconditional branch instructions
 */
static inline bool isUnconditionalBranch(MIR *insn)
{
    switch (insn->dalvikInsn.opcode) {
        case OP_RETURN_VOID:
        case OP_RETURN:
        case OP_RETURN_WIDE:
        case OP_RETURN_OBJECT:
            return true;
        default:
            return isGoto(insn);
    }
}

/*
 * dvmHashTableLookup() callback
 */
static int compareMethod(const CompilerMethodStats *m1,
                         const CompilerMethodStats *m2)
{
    return (int) m1->method - (int) m2->method;
}

/*
 * Analyze the body of the method to collect high-level information regarding
 * inlining:
 * - is empty method?
 * - is getter/setter?
 * - can throw exception?
 *
 * Currently the inliner only handles getters and setters. When its capability
 * becomes more sophisticated more information will be retrieved here.
 */
static int analyzeInlineTarget(DecodedInstruction *dalvikInsn, int attributes,
                               int offset)
{
    int flags = dexGetFlagsFromOpcode(dalvikInsn->opcode);
    int dalvikOpcode = dalvikInsn->opcode;

    if (flags & kInstrInvoke) {
        attributes &= ~METHOD_IS_LEAF;
    }

    if (!(flags & kInstrCanReturn)) {
        if (!(dvmCompilerDataFlowAttributes[dalvikOpcode] &
              DF_IS_GETTER)) {
            attributes &= ~METHOD_IS_GETTER;
        }
        if (!(dvmCompilerDataFlowAttributes[dalvikOpcode] &
              DF_IS_SETTER)) {
            attributes &= ~METHOD_IS_SETTER;
        }
    }

    /*
     * The expected instruction sequence is setter will never return value and
     * getter will also do. Clear the bits if the behavior is discovered
     * otherwise.
     */
    if (flags & kInstrCanReturn) {
        if (dalvikOpcode == OP_RETURN_VOID) {
            attributes &= ~METHOD_IS_GETTER;
        }
        else {
            attributes &= ~METHOD_IS_SETTER;
        }
    }

    if (flags & kInstrCanThrow) {
        attributes &= ~METHOD_IS_THROW_FREE;
    }

    if (offset == 0 && dalvikOpcode == OP_RETURN_VOID) {
        attributes |= METHOD_IS_EMPTY;
    }

    /*
     * Check if this opcode is selected for single stepping.
     * If so, don't inline the callee as there is no stack frame for the
     * interpreter to single-step through the instruction.
     */
    if (SINGLE_STEP_OP(dalvikOpcode)) {
        attributes &= ~(METHOD_IS_GETTER | METHOD_IS_SETTER);
    }

    return attributes;
}

/*
 * Analyze each method whose traces are ever compiled. Collect a variety of
 * statistics like the ratio of exercised vs overall code and code bloat
 * ratios. If isCallee is true, also analyze each instruction in more details
 * to see if it is suitable for inlining.
 */
CompilerMethodStats *dvmCompilerAnalyzeMethodBody(const Method *method,
                                                  bool isCallee)
{
    const DexCode *dexCode = dvmGetMethodCode(method);
    const u2 *codePtr = dexCode->insns;
    const u2 *codeEnd = dexCode->insns + dexCode->insnsSize;
    int insnSize = 0;
    int hashValue = dvmComputeUtf8Hash(method->name);

    CompilerMethodStats dummyMethodEntry; // For hash table lookup
    CompilerMethodStats *realMethodEntry; // For hash table storage

    /* For lookup only */
    dummyMethodEntry.method = method;
    realMethodEntry = (CompilerMethodStats *)
        dvmHashTableLookup(gDvmJit.methodStatsTable,
                           hashValue,
                           &dummyMethodEntry,
                           (HashCompareFunc) compareMethod,
                           false);

    /* This method has never been analyzed before - create an entry */
    if (realMethodEntry == NULL) {
        realMethodEntry =
            (CompilerMethodStats *) calloc(1, sizeof(CompilerMethodStats));
        realMethodEntry->method = method;

        dvmHashTableLookup(gDvmJit.methodStatsTable, hashValue,
                           realMethodEntry,
                           (HashCompareFunc) compareMethod,
                           true);
    }

    /* This method is invoked as a callee and has been analyzed - just return */
    if ((isCallee == true) && (realMethodEntry->attributes & METHOD_IS_CALLEE))
        return realMethodEntry;

    /*
     * Similarly, return if this method has been compiled before as a hot
     * method already.
     */
    if ((isCallee == false) &&
        (realMethodEntry->attributes & METHOD_IS_HOT))
        return realMethodEntry;

    int attributes;

    /* Method hasn't been analyzed for the desired purpose yet */
    if (isCallee) {
        /* Aggressively set the attributes until proven otherwise */
        attributes = METHOD_IS_LEAF | METHOD_IS_THROW_FREE | METHOD_IS_CALLEE |
                     METHOD_IS_GETTER | METHOD_IS_SETTER;
    } else {
        attributes = METHOD_IS_HOT;
    }

    /* Count the number of instructions */
    while (codePtr < codeEnd) {
        DecodedInstruction dalvikInsn;
        int width = parseInsn(codePtr, &dalvikInsn, false);

        /* Terminate when the data section is seen */
        if (width == 0)
            break;

        if (isCallee) {
            attributes = analyzeInlineTarget(&dalvikInsn, attributes, insnSize);
        }

        insnSize += width;
        codePtr += width;
    }

    /*
     * Only handle simple getters/setters with one instruction followed by
     * return
     */
    if ((attributes & (METHOD_IS_GETTER | METHOD_IS_SETTER)) &&
        (insnSize != 3)) {
        attributes &= ~(METHOD_IS_GETTER | METHOD_IS_SETTER);
    }

    realMethodEntry->dalvikSize = insnSize * 2;
    realMethodEntry->attributes |= attributes;

#if 0
    /* Uncomment the following to explore various callee patterns */
    if (attributes & METHOD_IS_THROW_FREE) {
        ALOGE("%s%s is inlinable%s", method->clazz->descriptor, method->name,
             (attributes & METHOD_IS_EMPTY) ? " empty" : "");
    }

    if (attributes & METHOD_IS_LEAF) {
        ALOGE("%s%s is leaf %d%s", method->clazz->descriptor, method->name,
             insnSize, insnSize < 5 ? " (small)" : "");
    }

    if (attributes & (METHOD_IS_GETTER | METHOD_IS_SETTER)) {
        ALOGE("%s%s is %s", method->clazz->descriptor, method->name,
             attributes & METHOD_IS_GETTER ? "getter": "setter");
    }
    if (attributes ==
        (METHOD_IS_LEAF | METHOD_IS_THROW_FREE | METHOD_IS_CALLEE)) {
        ALOGE("%s%s is inlinable non setter/getter", method->clazz->descriptor,
             method->name);
    }
#endif

    return realMethodEntry;
}

/*
 * Crawl the stack of the thread that requesed compilation to see if any of the
 * ancestors are on the blacklist.
 */
static bool filterMethodByCallGraph(Thread *thread, const char *curMethodName)
{
    /* Crawl the Dalvik stack frames and compare the method name*/
    StackSaveArea *ssaPtr = ((StackSaveArea *) thread->interpSave.curFrame) - 1;
    while (ssaPtr != ((StackSaveArea *) NULL) - 1) {
        const Method *method = ssaPtr->method;
        if (method) {
            int hashValue = dvmComputeUtf8Hash(method->name);
            bool found =
                dvmHashTableLookup(gDvmJit.methodTable, hashValue,
                               (char *) method->name,
                               (HashCompareFunc) strcmp, false) !=
                NULL;
            if (found) {
                ALOGD("Method %s (--> %s) found on the JIT %s list",
                     method->name, curMethodName,
                     gDvmJit.includeSelectedMethod ? "white" : "black");
                return true;
            }

        }
        ssaPtr = ((StackSaveArea *) ssaPtr->prevFrame) - 1;
    };
    return false;
}

/*
 * Since we are including instructions from possibly a cold method into the
 * current trace, we need to make sure that all the associated information
 * with the callee is properly initialized. If not, we punt on this inline
 * target.
 *
 * TODO: volatile instructions will be handled later.
 */
bool dvmCompilerCanIncludeThisInstruction(const Method *method,
                                          const DecodedInstruction *insn)
{
    switch (insn->opcode) {
        case OP_NEW_INSTANCE:
        case OP_CHECK_CAST: {
            ClassObject *classPtr = (ClassObject *)(void*)
              (method->clazz->pDvmDex->pResClasses[insn->vB]);

            /* Class hasn't been initialized yet */
            if (classPtr == NULL) {
                return false;
            }
            return true;
        }
        case OP_SGET:
        case OP_SGET_WIDE:
        case OP_SGET_OBJECT:
        case OP_SGET_BOOLEAN:
        case OP_SGET_BYTE:
        case OP_SGET_CHAR:
        case OP_SGET_SHORT:
        case OP_SPUT:
        case OP_SPUT_WIDE:
        case OP_SPUT_OBJECT:
        case OP_SPUT_BOOLEAN:
        case OP_SPUT_BYTE:
        case OP_SPUT_CHAR:
        case OP_SPUT_SHORT: {
            void *fieldPtr = (void*)
              (method->clazz->pDvmDex->pResFields[insn->vB]);

            if (fieldPtr == NULL) {
                return false;
            }
            return true;
        }
        case OP_INVOKE_SUPER:
        case OP_INVOKE_SUPER_RANGE: {
            int mIndex = method->clazz->pDvmDex->
                pResMethods[insn->vB]->methodIndex;
            const Method *calleeMethod = method->clazz->super->vtable[mIndex];
            if (calleeMethod == NULL) {
                return false;
            }
            return true;
        }
        case OP_INVOKE_SUPER_QUICK:
        case OP_INVOKE_SUPER_QUICK_RANGE: {
            const Method *calleeMethod = method->clazz->super->vtable[insn->vB];
            if (calleeMethod == NULL) {
                return false;
            }
            return true;
        }
        case OP_INVOKE_STATIC:
        case OP_INVOKE_STATIC_RANGE:
        case OP_INVOKE_DIRECT:
        case OP_INVOKE_DIRECT_RANGE: {
            const Method *calleeMethod =
                method->clazz->pDvmDex->pResMethods[insn->vB];
            if (calleeMethod == NULL) {
                return false;
            }
            return true;
        }
        case OP_CONST_CLASS: {
            void *classPtr = (void*)
                (method->clazz->pDvmDex->pResClasses[insn->vB]);

            if (classPtr == NULL) {
                return false;
            }
            return true;
        }
        case OP_CONST_STRING_JUMBO:
        case OP_CONST_STRING: {
            void *strPtr = (void*)
                (method->clazz->pDvmDex->pResStrings[insn->vB]);

            if (strPtr == NULL) {
                return false;
            }
            return true;
        }
        default:
            return true;
    }
}

/* Split an existing block from the specified code offset into two */
static BasicBlock *splitBlock(CompilationUnit *cUnit,
                              unsigned int codeOffset,
                              BasicBlock *origBlock,
                              BasicBlock **immedPredBlockP)
{
    MIR *insn = origBlock->firstMIRInsn;
    while (insn) {
        if (insn->offset == codeOffset) break;
        insn = insn->next;
    }
    if (insn == NULL) {
        ALOGE("Break split failed");
        dvmAbort();
    }
    BasicBlock *bottomBlock = dvmCompilerNewBB(kDalvikByteCode,
                                               cUnit->numBlocks++);
    dvmInsertGrowableList(&cUnit->blockList, (intptr_t) bottomBlock);

    bottomBlock->startOffset = codeOffset;
    bottomBlock->firstMIRInsn = insn;
    bottomBlock->lastMIRInsn = origBlock->lastMIRInsn;

    /* Handle the taken path */
    bottomBlock->taken = origBlock->taken;
    if (bottomBlock->taken) {
        origBlock->taken = NULL;
        dvmCompilerClearBit(bottomBlock->taken->predecessors, origBlock->id);
        dvmCompilerSetBit(bottomBlock->taken->predecessors, bottomBlock->id);
    }

    /* Handle the fallthrough path */
    bottomBlock->needFallThroughBranch = origBlock->needFallThroughBranch;
    bottomBlock->fallThrough = origBlock->fallThrough;
    origBlock->fallThrough = bottomBlock;
    origBlock->needFallThroughBranch = true;
    dvmCompilerSetBit(bottomBlock->predecessors, origBlock->id);
    if (bottomBlock->fallThrough) {
        dvmCompilerClearBit(bottomBlock->fallThrough->predecessors,
                            origBlock->id);
        dvmCompilerSetBit(bottomBlock->fallThrough->predecessors,
                          bottomBlock->id);
    }

    /* Handle the successor list */
    if (origBlock->successorBlockList.blockListType != kNotUsed) {
        bottomBlock->successorBlockList = origBlock->successorBlockList;
        origBlock->successorBlockList.blockListType = kNotUsed;
        GrowableListIterator iterator;

        dvmGrowableListIteratorInit(&bottomBlock->successorBlockList.blocks,
                                    &iterator);
        while (true) {
            SuccessorBlockInfo *successorBlockInfo =
                (SuccessorBlockInfo *) dvmGrowableListIteratorNext(&iterator);
            if (successorBlockInfo == NULL) break;
            BasicBlock *bb = successorBlockInfo->block;
            dvmCompilerClearBit(bb->predecessors, origBlock->id);
            dvmCompilerSetBit(bb->predecessors, bottomBlock->id);
        }
    }

    origBlock->lastMIRInsn = insn->prev;

    insn->prev->next = NULL;
    insn->prev = NULL;

    /*
     * Update the immediate predecessor block pointer so that outgoing edges
     * can be applied to the proper block.
     */
    if (immedPredBlockP) {
        assert(*immedPredBlockP == origBlock);
        *immedPredBlockP = bottomBlock;
    }
    return bottomBlock;
}

/*
 * Given a code offset, find out the block that starts with it. If the offset
 * is in the middle of an existing block, split it into two. If immedPredBlockP
 * is non-null and is the block being split, update *immedPredBlockP to point
 * to the bottom block so that outgoing edges can be setup properly (by the
 * caller).
 */
static BasicBlock *findBlock(CompilationUnit *cUnit,
                             unsigned int codeOffset,
                             bool split, bool create,
                             BasicBlock **immedPredBlockP)
{
    GrowableList *blockList = &cUnit->blockList;
    BasicBlock *bb;
    unsigned int i;

    for (i = 0; i < blockList->numUsed; i++) {
        bb = (BasicBlock *) blockList->elemList[i];
        if (bb->blockType != kDalvikByteCode) continue;
        if (bb->startOffset == codeOffset) return bb;
        /* Check if a branch jumps into the middle of an existing block */
        if ((split == true) && (codeOffset > bb->startOffset) &&
            (bb->lastMIRInsn != NULL) &&
            (codeOffset <= bb->lastMIRInsn->offset)) {
            BasicBlock *newBB = splitBlock(cUnit, codeOffset, bb,
                                           bb == *immedPredBlockP ?
                                               immedPredBlockP : NULL);
            return newBB;
        }
    }
    if (create) {
          bb = dvmCompilerNewBB(kDalvikByteCode, cUnit->numBlocks++);
          dvmInsertGrowableList(&cUnit->blockList, (intptr_t) bb);
          bb->startOffset = codeOffset;
          return bb;
    }
    return NULL;
}

/* Dump the CFG into a DOT graph */
void dvmDumpCFG(CompilationUnit *cUnit, const char *dirPrefix)
{
    const Method *method = cUnit->method;
    FILE *file;
    char *signature = dexProtoCopyMethodDescriptor(&method->prototype);
    char startOffset[80];
    sprintf(startOffset, "_%x", cUnit->entryBlock->fallThrough->startOffset);
    char *fileName = (char *) dvmCompilerNew(
                                  strlen(dirPrefix) +
                                  strlen(method->clazz->descriptor) +
                                  strlen(method->name) +
                                  strlen(signature) +
                                  strlen(startOffset) +
                                  strlen(".dot") + 1, true);
    sprintf(fileName, "%s%s%s%s%s.dot", dirPrefix,
            method->clazz->descriptor, method->name, signature, startOffset);
    free(signature);

    /*
     * Convert the special characters into a filesystem- and shell-friendly
     * format.
     */
    int i;
    for (i = strlen(dirPrefix); fileName[i]; i++) {
        if (fileName[i] == '/') {
            fileName[i] = '_';
        } else if (fileName[i] == ';') {
            fileName[i] = '#';
        } else if (fileName[i] == '$') {
            fileName[i] = '+';
        } else if (fileName[i] == '(' || fileName[i] == ')') {
            fileName[i] = '@';
        } else if (fileName[i] == '<' || fileName[i] == '>') {
            fileName[i] = '=';
        }
    }
    file = fopen(fileName, "w");
    if (file == NULL) {
        return;
    }
    fprintf(file, "digraph G {\n");

    fprintf(file, "  rankdir=TB\n");

    int numReachableBlocks = cUnit->numReachableBlocks;
    int idx;
    const GrowableList *blockList = &cUnit->blockList;

    for (idx = 0; idx < numReachableBlocks; idx++) {
        int blockIdx = cUnit->dfsOrder.elemList[idx];
        BasicBlock *bb = (BasicBlock *) dvmGrowableListGetElement(blockList,
                                                                  blockIdx);
        if (bb == NULL) break;
        if (bb->blockType == kEntryBlock) {
            fprintf(file, "  entry [shape=Mdiamond];\n");
        } else if (bb->blockType == kExitBlock) {
            fprintf(file, "  exit [shape=Mdiamond];\n");
        } else if (bb->blockType == kDalvikByteCode) {
            fprintf(file, "  block%04x [shape=record,label = \"{ \\\n",
                    bb->startOffset);
            const MIR *mir;
            fprintf(file, "    {block id %d\\l}%s\\\n", bb->id,
                    bb->firstMIRInsn ? " | " : " ");
            for (mir = bb->firstMIRInsn; mir; mir = mir->next) {
                fprintf(file, "    {%04x %s\\l}%s\\\n", mir->offset,
                        mir->ssaRep ?
                            dvmCompilerFullDisassembler(cUnit, mir) :
                            dexGetOpcodeName(mir->dalvikInsn.opcode),
                        mir->next ? " | " : " ");
            }
            fprintf(file, "  }\"];\n\n");
        } else if (bb->blockType == kExceptionHandling) {
            char blockName[BLOCK_NAME_LEN];

            dvmGetBlockName(bb, blockName);
            fprintf(file, "  %s [shape=invhouse];\n", blockName);
        }

        char blockName1[BLOCK_NAME_LEN], blockName2[BLOCK_NAME_LEN];

        if (bb->taken) {
            dvmGetBlockName(bb, blockName1);
            dvmGetBlockName(bb->taken, blockName2);
            fprintf(file, "  %s:s -> %s:n [style=dotted]\n",
                    blockName1, blockName2);
        }
        if (bb->fallThrough) {
            dvmGetBlockName(bb, blockName1);
            dvmGetBlockName(bb->fallThrough, blockName2);
            fprintf(file, "  %s:s -> %s:n\n", blockName1, blockName2);
        }

        if (bb->successorBlockList.blockListType != kNotUsed) {
            fprintf(file, "  succ%04x [shape=%s,label = \"{ \\\n",
                    bb->startOffset,
                    (bb->successorBlockList.blockListType == kCatch) ?
                        "Mrecord" : "record");
            GrowableListIterator iterator;
            dvmGrowableListIteratorInit(&bb->successorBlockList.blocks,
                                        &iterator);
            SuccessorBlockInfo *successorBlockInfo =
                (SuccessorBlockInfo *) dvmGrowableListIteratorNext(&iterator);

            int succId = 0;
            while (true) {
                if (successorBlockInfo == NULL) break;

                BasicBlock *destBlock = successorBlockInfo->block;
                SuccessorBlockInfo *nextSuccessorBlockInfo =
                  (SuccessorBlockInfo *) dvmGrowableListIteratorNext(&iterator);

                fprintf(file, "    {<f%d> %04x: %04x\\l}%s\\\n",
                        succId++,
                        successorBlockInfo->key,
                        destBlock->startOffset,
                        (nextSuccessorBlockInfo != NULL) ? " | " : " ");

                successorBlockInfo = nextSuccessorBlockInfo;
            }
            fprintf(file, "  }\"];\n\n");

            dvmGetBlockName(bb, blockName1);
            fprintf(file, "  %s:s -> succ%04x:n [style=dashed]\n",
                    blockName1, bb->startOffset);

            if (bb->successorBlockList.blockListType == kPackedSwitch ||
                bb->successorBlockList.blockListType == kSparseSwitch) {

                dvmGrowableListIteratorInit(&bb->successorBlockList.blocks,
                                            &iterator);

                succId = 0;
                while (true) {
                    SuccessorBlockInfo *successorBlockInfo =
                        (SuccessorBlockInfo *)
                            dvmGrowableListIteratorNext(&iterator);
                    if (successorBlockInfo == NULL) break;

                    BasicBlock *destBlock = successorBlockInfo->block;

                    dvmGetBlockName(destBlock, blockName2);
                    fprintf(file, "  succ%04x:f%d:e -> %s:n\n",
                            bb->startOffset, succId++,
                            blockName2);
                }
            }
        }
        fprintf(file, "\n");

        /*
         * If we need to debug the dominator tree, uncomment the following code
         */
#if 1
        dvmGetBlockName(bb, blockName1);
        fprintf(file, "  cfg%s [label=\"%s\", shape=none];\n",
                blockName1, blockName1);
        if (bb->iDom) {
            dvmGetBlockName(bb->iDom, blockName2);
            fprintf(file, "  cfg%s:s -> cfg%s:n\n\n",
                    blockName2, blockName1);
        }
#endif
    }
    fprintf(file, "}\n");
    fclose(file);
}

/* Verify if all the successor is connected with all the claimed predecessors */
static bool verifyPredInfo(CompilationUnit *cUnit, BasicBlock *bb)
{
    BitVectorIterator bvIterator;

    dvmBitVectorIteratorInit(bb->predecessors, &bvIterator);
    while (true) {
        int blockIdx = dvmBitVectorIteratorNext(&bvIterator);
        if (blockIdx == -1) break;
        BasicBlock *predBB = (BasicBlock *)
            dvmGrowableListGetElement(&cUnit->blockList, blockIdx);
        bool found = false;
        if (predBB->taken == bb) {
            found = true;
        } else if (predBB->fallThrough == bb) {
            found = true;
        } else if (predBB->successorBlockList.blockListType != kNotUsed) {
            GrowableListIterator iterator;
            dvmGrowableListIteratorInit(&predBB->successorBlockList.blocks,
                                        &iterator);
            while (true) {
                SuccessorBlockInfo *successorBlockInfo =
                    (SuccessorBlockInfo *)
                        dvmGrowableListIteratorNext(&iterator);
                if (successorBlockInfo == NULL) break;
                BasicBlock *succBB = successorBlockInfo->block;
                if (succBB == bb) {
                    found = true;
                    break;
                }
            }
        }
        if (found == false) {
            char blockName1[BLOCK_NAME_LEN], blockName2[BLOCK_NAME_LEN];
            dvmGetBlockName(bb, blockName1);
            dvmGetBlockName(predBB, blockName2);
            dvmDumpCFG(cUnit, "/sdcard/cfg/");
            ALOGE("Successor %s not found from %s",
                 blockName1, blockName2);
            dvmAbort();
        }
    }
    return true;
}

/* Identify code range in try blocks and set up the empty catch blocks */
static void processTryCatchBlocks(CompilationUnit *cUnit)
{
    const Method *meth = cUnit->method;
    const DexCode *pCode = dvmGetMethodCode(meth);
    int triesSize = pCode->triesSize;
    int i;
    int offset;

    if (triesSize == 0) {
        return;
    }

    const DexTry *pTries = dexGetTries(pCode);
    BitVector *tryBlockAddr = cUnit->tryBlockAddr;

    /* Mark all the insn offsets in Try blocks */
    for (i = 0; i < triesSize; i++) {
        const DexTry* pTry = &pTries[i];
        /* all in 16-bit units */
        int startOffset = pTry->startAddr;
        int endOffset = startOffset + pTry->insnCount;

        for (offset = startOffset; offset < endOffset; offset++) {
            dvmCompilerSetBit(tryBlockAddr, offset);
        }
    }

    /* Iterate over each of the handlers to enqueue the empty Catch blocks */
    offset = dexGetFirstHandlerOffset(pCode);
    int handlersSize = dexGetHandlersSize(pCode);

    for (i = 0; i < handlersSize; i++) {
        DexCatchIterator iterator;
        dexCatchIteratorInit(&iterator, pCode, offset);

        for (;;) {
            DexCatchHandler* handler = dexCatchIteratorNext(&iterator);

            if (handler == NULL) {
                break;
            }

            /*
             * Create dummy catch blocks first. Since these are created before
             * other blocks are processed, "split" is specified as false.
             */
            findBlock(cUnit, handler->address,
                      /* split */
                      false,
                      /* create */
                      true,
                      /* immedPredBlockP */
                      NULL);
        }

        offset = dexCatchIteratorGetEndOffset(&iterator, pCode);
    }
}

/* Process instructions with the kInstrCanBranch flag */
static void processCanBranch(CompilationUnit *cUnit, BasicBlock *curBlock,
                             MIR *insn, int curOffset, int width, int flags,
                             const u2* codePtr, const u2* codeEnd)
{
    int target = curOffset;
    switch (insn->dalvikInsn.opcode) {
        case OP_GOTO:
        case OP_GOTO_16:
        case OP_GOTO_32:
            target += (int) insn->dalvikInsn.vA;
            break;
        case OP_IF_EQ:
        case OP_IF_NE:
        case OP_IF_LT:
        case OP_IF_GE:
        case OP_IF_GT:
        case OP_IF_LE:
            target += (int) insn->dalvikInsn.vC;
            break;
        case OP_IF_EQZ:
        case OP_IF_NEZ:
        case OP_IF_LTZ:
        case OP_IF_GEZ:
        case OP_IF_GTZ:
        case OP_IF_LEZ:
            target += (int) insn->dalvikInsn.vB;
            break;
        default:
            ALOGE("Unexpected opcode(%d) with kInstrCanBranch set",
                 insn->dalvikInsn.opcode);
            dvmAbort();
    }
    BasicBlock *takenBlock = findBlock(cUnit, target,
                                       /* split */
                                       true,
                                       /* create */
                                       true,
                                       /* immedPredBlockP */
                                       &curBlock);
    curBlock->taken = takenBlock;
    dvmCompilerSetBit(takenBlock->predecessors, curBlock->id);

    /* Always terminate the current block for conditional branches */
    if (flags & kInstrCanContinue) {
        BasicBlock *fallthroughBlock = findBlock(cUnit,
                                                 curOffset +  width,
                                                 /*
                                                  * If the method is processed
                                                  * in sequential order from the
                                                  * beginning, we don't need to
                                                  * specify split for continue
                                                  * blocks. However, this
                                                  * routine can be called by
                                                  * compileLoop, which starts
                                                  * parsing the method from an
                                                  * arbitrary address in the
                                                  * method body.
                                                  */
                                                 true,
                                                 /* create */
                                                 true,
                                                 /* immedPredBlockP */
                                                 &curBlock);
        curBlock->fallThrough = fallthroughBlock;
        dvmCompilerSetBit(fallthroughBlock->predecessors, curBlock->id);
    } else if (codePtr < codeEnd) {
        /* Create a fallthrough block for real instructions (incl. OP_NOP) */
        if (contentIsInsn(codePtr)) {
            findBlock(cUnit, curOffset + width,
                      /* split */
                      false,
                      /* create */
                      true,
                      /* immedPredBlockP */
                      NULL);
        }
    }
}

/* Process instructions with the kInstrCanSwitch flag */
static void processCanSwitch(CompilationUnit *cUnit, BasicBlock *curBlock,
                             MIR *insn, int curOffset, int width, int flags)
{
    u2 *switchData= (u2 *) (cUnit->method->insns + curOffset +
                            insn->dalvikInsn.vB);
    int size;
    int *keyTable;
    int *targetTable;
    int i;
    int firstKey;

    /*
     * Packed switch data format:
     *  ushort ident = 0x0100   magic value
     *  ushort size             number of entries in the table
     *  int first_key           first (and lowest) switch case value
     *  int targets[size]       branch targets, relative to switch opcode
     *
     * Total size is (4+size*2) 16-bit code units.
     */
    if (insn->dalvikInsn.opcode == OP_PACKED_SWITCH) {
        assert(switchData[0] == kPackedSwitchSignature);
        size = switchData[1];
        firstKey = switchData[2] | (switchData[3] << 16);
        targetTable = (int *) &switchData[4];
        keyTable = NULL;        // Make the compiler happy
    /*
     * Sparse switch data format:
     *  ushort ident = 0x0200   magic value
     *  ushort size             number of entries in the table; > 0
     *  int keys[size]          keys, sorted low-to-high; 32-bit aligned
     *  int targets[size]       branch targets, relative to switch opcode
     *
     * Total size is (2+size*4) 16-bit code units.
     */
    } else {
        assert(switchData[0] == kSparseSwitchSignature);
        size = switchData[1];
        keyTable = (int *) &switchData[2];
        targetTable = (int *) &switchData[2 + size*2];
        firstKey = 0;   // To make the compiler happy
    }

    if (curBlock->successorBlockList.blockListType != kNotUsed) {
        ALOGE("Successor block list already in use: %d",
             curBlock->successorBlockList.blockListType);
        dvmAbort();
    }
    curBlock->successorBlockList.blockListType =
        (insn->dalvikInsn.opcode == OP_PACKED_SWITCH) ?
        kPackedSwitch : kSparseSwitch;
    dvmInitGrowableList(&curBlock->successorBlockList.blocks, size);

    for (i = 0; i < size; i++) {
        BasicBlock *caseBlock = findBlock(cUnit, curOffset + targetTable[i],
                                          /* split */
                                          true,
                                          /* create */
                                          true,
                                          /* immedPredBlockP */
                                          &curBlock);
        SuccessorBlockInfo *successorBlockInfo =
            (SuccessorBlockInfo *) dvmCompilerNew(sizeof(SuccessorBlockInfo),
                                                  false);
        successorBlockInfo->block = caseBlock;
        successorBlockInfo->key = (insn->dalvikInsn.opcode == OP_PACKED_SWITCH)?
                                  firstKey + i : keyTable[i];
        dvmInsertGrowableList(&curBlock->successorBlockList.blocks,
                              (intptr_t) successorBlockInfo);
        dvmCompilerSetBit(caseBlock->predecessors, curBlock->id);
    }

    /* Fall-through case */
    BasicBlock *fallthroughBlock = findBlock(cUnit,
                                             curOffset +  width,
                                             /* split */
                                             false,
                                             /* create */
                                             true,
                                             /* immedPredBlockP */
                                             NULL);
    curBlock->fallThrough = fallthroughBlock;
    dvmCompilerSetBit(fallthroughBlock->predecessors, curBlock->id);
}

/* Process instructions with the kInstrCanThrow flag */
static void processCanThrow(CompilationUnit *cUnit, BasicBlock *curBlock,
                            MIR *insn, int curOffset, int width, int flags,
                            BitVector *tryBlockAddr, const u2 *codePtr,
                            const u2* codeEnd)
{
    const Method *method = cUnit->method;
    const DexCode *dexCode = dvmGetMethodCode(method);

    /* In try block */
    if (dvmIsBitSet(tryBlockAddr, curOffset)) {
        DexCatchIterator iterator;

        if (!dexFindCatchHandler(&iterator, dexCode, curOffset)) {
            ALOGE("Catch block not found in dexfile for insn %x in %s",
                 curOffset, method->name);
            dvmAbort();

        }
        if (curBlock->successorBlockList.blockListType != kNotUsed) {
            ALOGE("Successor block list already in use: %d",
                 curBlock->successorBlockList.blockListType);
            dvmAbort();
        }
        curBlock->successorBlockList.blockListType = kCatch;
        dvmInitGrowableList(&curBlock->successorBlockList.blocks, 2);

        for (;;) {
            DexCatchHandler* handler = dexCatchIteratorNext(&iterator);

            if (handler == NULL) {
                break;
            }

            BasicBlock *catchBlock = findBlock(cUnit, handler->address,
                                               /* split */
                                               false,
                                               /* create */
                                               false,
                                               /* immedPredBlockP */
                                               NULL);

            SuccessorBlockInfo *successorBlockInfo =
              (SuccessorBlockInfo *) dvmCompilerNew(sizeof(SuccessorBlockInfo),
                                                    false);
            successorBlockInfo->block = catchBlock;
            successorBlockInfo->key = handler->typeIdx;
            dvmInsertGrowableList(&curBlock->successorBlockList.blocks,
                                  (intptr_t) successorBlockInfo);
            dvmCompilerSetBit(catchBlock->predecessors, curBlock->id);
        }
    } else {
        BasicBlock *ehBlock = dvmCompilerNewBB(kExceptionHandling,
                                               cUnit->numBlocks++);
        curBlock->taken = ehBlock;
        dvmInsertGrowableList(&cUnit->blockList, (intptr_t) ehBlock);
        ehBlock->startOffset = curOffset;
        dvmCompilerSetBit(ehBlock->predecessors, curBlock->id);
    }

    /*
     * Force the current block to terminate.
     *
     * Data may be present before codeEnd, so we need to parse it to know
     * whether it is code or data.
     */
    if (codePtr < codeEnd) {
        /* Create a fallthrough block for real instructions (incl. OP_NOP) */
        if (contentIsInsn(codePtr)) {
            BasicBlock *fallthroughBlock = findBlock(cUnit,
                                                     curOffset + width,
                                                     /* split */
                                                     false,
                                                     /* create */
                                                     true,
                                                     /* immedPredBlockP */
                                                     NULL);
            /*
             * OP_THROW and OP_THROW_VERIFICATION_ERROR are unconditional
             * branches.
             */
            if (insn->dalvikInsn.opcode != OP_THROW_VERIFICATION_ERROR &&
                insn->dalvikInsn.opcode != OP_THROW) {
                curBlock->fallThrough = fallthroughBlock;
                dvmCompilerSetBit(fallthroughBlock->predecessors, curBlock->id);
            }
        }
    }
}

/*
 * Similar to dvmCompileTrace, but the entity processed here is the whole
 * method.
 *
 * TODO: implementation will be revisited when the trace builder can provide
 * whole-method traces.
 */
bool dvmCompileMethod(const Method *method, JitTranslationInfo *info)
{
    CompilationUnit cUnit;
    const DexCode *dexCode = dvmGetMethodCode(method);
    const u2 *codePtr = dexCode->insns;
    const u2 *codeEnd = dexCode->insns + dexCode->insnsSize;
    int numBlocks = 0;
    unsigned int curOffset = 0;

    /* Method already compiled */
    if (dvmJitGetMethodAddr(codePtr)) {
        info->codeAddress = NULL;
        return false;
    }

    memset(&cUnit, 0, sizeof(cUnit));
    cUnit.method = method;

    cUnit.jitMode = kJitMethod;

    /* Initialize the block list */
    dvmInitGrowableList(&cUnit.blockList, 4);

    /*
     * FIXME - PC reconstruction list won't be needed after the codegen routines
     * are enhanced to true method mode.
     */
    /* Initialize the PC reconstruction list */
    dvmInitGrowableList(&cUnit.pcReconstructionList, 8);

    /* Allocate the bit-vector to track the beginning of basic blocks */
    BitVector *tryBlockAddr = dvmCompilerAllocBitVector(dexCode->insnsSize,
                                                        true /* expandable */);
    cUnit.tryBlockAddr = tryBlockAddr;

    /* Create the default entry and exit blocks and enter them to the list */
    BasicBlock *entryBlock = dvmCompilerNewBB(kEntryBlock, numBlocks++);
    BasicBlock *exitBlock = dvmCompilerNewBB(kExitBlock, numBlocks++);

    cUnit.entryBlock = entryBlock;
    cUnit.exitBlock = exitBlock;

    dvmInsertGrowableList(&cUnit.blockList, (intptr_t) entryBlock);
    dvmInsertGrowableList(&cUnit.blockList, (intptr_t) exitBlock);

    /* Current block to record parsed instructions */
    BasicBlock *curBlock = dvmCompilerNewBB(kDalvikByteCode, numBlocks++);
    curBlock->startOffset = 0;
    dvmInsertGrowableList(&cUnit.blockList, (intptr_t) curBlock);
    entryBlock->fallThrough = curBlock;
    dvmCompilerSetBit(curBlock->predecessors, entryBlock->id);

    /*
     * Store back the number of blocks since new blocks may be created of
     * accessing cUnit.
     */
    cUnit.numBlocks = numBlocks;

    /* Identify code range in try blocks and set up the empty catch blocks */
    processTryCatchBlocks(&cUnit);

    /* Parse all instructions and put them into containing basic blocks */
    while (codePtr < codeEnd) {
        MIR *insn = (MIR *) dvmCompilerNew(sizeof(MIR), true);
        insn->offset = curOffset;
        int width = parseInsn(codePtr, &insn->dalvikInsn, false);
        insn->width = width;

        /* Terminate when the data section is seen */
        if (width == 0)
            break;

        dvmCompilerAppendMIR(curBlock, insn);

        codePtr += width;
        int flags = dexGetFlagsFromOpcode(insn->dalvikInsn.opcode);

        if (flags & kInstrCanBranch) {
            processCanBranch(&cUnit, curBlock, insn, curOffset, width, flags,
                             codePtr, codeEnd);
        } else if (flags & kInstrCanReturn) {
            curBlock->fallThrough = exitBlock;
            dvmCompilerSetBit(exitBlock->predecessors, curBlock->id);
            /*
             * Terminate the current block if there are instructions
             * afterwards.
             */
            if (codePtr < codeEnd) {
                /*
                 * Create a fallthrough block for real instructions
                 * (incl. OP_NOP).
                 */
                if (contentIsInsn(codePtr)) {
                    findBlock(&cUnit, curOffset + width,
                              /* split */
                              false,
                              /* create */
                              true,
                              /* immedPredBlockP */
                              NULL);
                }
            }
        } else if (flags & kInstrCanThrow) {
            processCanThrow(&cUnit, curBlock, insn, curOffset, width, flags,
                            tryBlockAddr, codePtr, codeEnd);
        } else if (flags & kInstrCanSwitch) {
            processCanSwitch(&cUnit, curBlock, insn, curOffset, width, flags);
        }
        curOffset += width;
        BasicBlock *nextBlock = findBlock(&cUnit, curOffset,
                                          /* split */
                                          false,
                                          /* create */
                                          false,
                                          /* immedPredBlockP */
                                          NULL);
        if (nextBlock) {
            /*
             * The next instruction could be the target of a previously parsed
             * forward branch so a block is already created. If the current
             * instruction is not an unconditional branch, connect them through
             * the fall-through link.
             */
            assert(curBlock->fallThrough == NULL ||
                   curBlock->fallThrough == nextBlock ||
                   curBlock->fallThrough == exitBlock);

            if ((curBlock->fallThrough == NULL) &&
                (flags & kInstrCanContinue)) {
                curBlock->fallThrough = nextBlock;
                dvmCompilerSetBit(nextBlock->predecessors, curBlock->id);
            }
            curBlock = nextBlock;
        }
    }

    if (cUnit.printMe) {
        dvmCompilerDumpCompilationUnit(&cUnit);
    }

    /* Adjust this value accordingly once inlining is performed */
    cUnit.numDalvikRegisters = cUnit.method->registersSize;

    /* Verify if all blocks are connected as claimed */
    /* FIXME - to be disabled in the future */
    dvmCompilerDataFlowAnalysisDispatcher(&cUnit, verifyPredInfo,
                                          kAllNodes,
                                          false /* isIterative */);


    /* Perform SSA transformation for the whole method */
    dvmCompilerMethodSSATransformation(&cUnit);

    dvmCompilerInitializeRegAlloc(&cUnit);  // Needs to happen after SSA naming

    /* Allocate Registers using simple local allocation scheme */
    dvmCompilerLocalRegAlloc(&cUnit);

    /* Convert MIR to LIR, etc. */
    dvmCompilerMethodMIR2LIR(&cUnit);

    // Debugging only
    //dvmDumpCFG(&cUnit, "/sdcard/cfg/");

    /* Method is not empty */
    if (cUnit.firstLIRInsn) {
        /* Convert LIR into machine code. Loop for recoverable retries */
        do {
            dvmCompilerAssembleLIR(&cUnit, info);
            cUnit.assemblerRetries++;
            if (cUnit.printMe && cUnit.assemblerStatus != kSuccess)
                ALOGD("Assembler abort #%d on %d",cUnit.assemblerRetries,
                      cUnit.assemblerStatus);
        } while (cUnit.assemblerStatus == kRetryAll);

        if (cUnit.printMe) {
            dvmCompilerCodegenDump(&cUnit);
        }

        if (info->codeAddress) {
            dvmJitSetCodeAddr(dexCode->insns, info->codeAddress,
                              info->instructionSet, true, 0);
            /*
             * Clear the codeAddress for the enclosing trace to reuse the info
             */
            info->codeAddress = NULL;
        }
    }

    return false;
}

/* Extending the trace by crawling the code from curBlock */
static bool exhaustTrace(CompilationUnit *cUnit, BasicBlock *curBlock)
{
    unsigned int curOffset = curBlock->startOffset;
    const u2 *codePtr = cUnit->method->insns + curOffset;

    if (curBlock->visited == true) return false;

    curBlock->visited = true;

    if (curBlock->blockType == kEntryBlock ||
        curBlock->blockType == kExitBlock) {
        return false;
    }

    /*
     * Block has been parsed - check the taken/fallThrough in case it is a split
     * block.
     */
    if (curBlock->firstMIRInsn != NULL) {
          bool changed = false;
          if (curBlock->taken)
              changed |= exhaustTrace(cUnit, curBlock->taken);
          if (curBlock->fallThrough)
              changed |= exhaustTrace(cUnit, curBlock->fallThrough);
          return changed;
    }
    while (true) {
        MIR *insn = (MIR *) dvmCompilerNew(sizeof(MIR), true);
        insn->offset = curOffset;
        int width = parseInsn(codePtr, &insn->dalvikInsn, false);
        insn->width = width;

        /* Terminate when the data section is seen */
        if (width == 0)
            break;

        dvmCompilerAppendMIR(curBlock, insn);

        codePtr += width;
        int flags = dexGetFlagsFromOpcode(insn->dalvikInsn.opcode);

        /* Stop extending the trace after seeing these instructions */
        if (flags & (kInstrCanReturn | kInstrCanSwitch | kInstrInvoke)) {
            curBlock->fallThrough = cUnit->exitBlock;
            dvmCompilerSetBit(cUnit->exitBlock->predecessors, curBlock->id);
            break;
        } else if (flags & kInstrCanBranch) {
            processCanBranch(cUnit, curBlock, insn, curOffset, width, flags,
                             codePtr, NULL);
            if (curBlock->taken) {
                exhaustTrace(cUnit, curBlock->taken);
            }
            if (curBlock->fallThrough) {
                exhaustTrace(cUnit, curBlock->fallThrough);
            }
            break;
        }
        curOffset += width;
        BasicBlock *nextBlock = findBlock(cUnit, curOffset,
                                          /* split */
                                          false,
                                          /* create */
                                          false,
                                          /* immedPredBlockP */
                                          NULL);
        if (nextBlock) {
            /*
             * The next instruction could be the target of a previously parsed
             * forward branch so a block is already created. If the current
             * instruction is not an unconditional branch, connect them through
             * the fall-through link.
             */
            assert(curBlock->fallThrough == NULL ||
                   curBlock->fallThrough == nextBlock ||
                   curBlock->fallThrough == cUnit->exitBlock);

            if ((curBlock->fallThrough == NULL) &&
                (flags & kInstrCanContinue)) {
                curBlock->needFallThroughBranch = true;
                curBlock->fallThrough = nextBlock;
                dvmCompilerSetBit(nextBlock->predecessors, curBlock->id);
            }
            /* Block has been visited - no more parsing needed */
            if (nextBlock->visited == true) {
                return true;
            }
            curBlock = nextBlock;
        }
    }
    return true;
}

/* Compile a loop */
static bool compileLoop(CompilationUnit *cUnit, unsigned int startOffset,
                        JitTraceDescription *desc, int numMaxInsts,
                        JitTranslationInfo *info, jmp_buf *bailPtr,
                        int optHints)
{
    int numBlocks = 0;
    unsigned int curOffset = startOffset;
    bool changed;
    BasicBlock *bb;
#if defined(WITH_JIT_TUNING)
    CompilerMethodStats *methodStats;
#endif

    cUnit->jitMode = kJitLoop;

    /* Initialize the block list */
    dvmInitGrowableList(&cUnit->blockList, 4);

    /* Initialize the PC reconstruction list */
    dvmInitGrowableList(&cUnit->pcReconstructionList, 8);

    /* Create the default entry and exit blocks and enter them to the list */
    BasicBlock *entryBlock = dvmCompilerNewBB(kEntryBlock, numBlocks++);
    entryBlock->startOffset = curOffset;
    BasicBlock *exitBlock = dvmCompilerNewBB(kExitBlock, numBlocks++);

    cUnit->entryBlock = entryBlock;
    cUnit->exitBlock = exitBlock;

    dvmInsertGrowableList(&cUnit->blockList, (intptr_t) entryBlock);
    dvmInsertGrowableList(&cUnit->blockList, (intptr_t) exitBlock);

    /* Current block to record parsed instructions */
    BasicBlock *curBlock = dvmCompilerNewBB(kDalvikByteCode, numBlocks++);
    curBlock->startOffset = curOffset;

    dvmInsertGrowableList(&cUnit->blockList, (intptr_t) curBlock);
    entryBlock->fallThrough = curBlock;
    dvmCompilerSetBit(curBlock->predecessors, entryBlock->id);

    /*
     * Store back the number of blocks since new blocks may be created of
     * accessing cUnit.
     */
    cUnit->numBlocks = numBlocks;

    do {
        dvmCompilerDataFlowAnalysisDispatcher(cUnit,
                                              dvmCompilerClearVisitedFlag,
                                              kAllNodes,
                                              false /* isIterative */);
        changed = exhaustTrace(cUnit, curBlock);
    } while (changed);

    /* Backward chaining block */
    bb = dvmCompilerNewBB(kChainingCellBackwardBranch, cUnit->numBlocks++);
    dvmInsertGrowableList(&cUnit->blockList, (intptr_t) bb);
    cUnit->backChainBlock = bb;

    /* A special block to host PC reconstruction code */
    bb = dvmCompilerNewBB(kPCReconstruction, cUnit->numBlocks++);
    dvmInsertGrowableList(&cUnit->blockList, (intptr_t) bb);

    /* And one final block that publishes the PC ancodeAddressd raises the exception */
    bb = dvmCompilerNewBB(kExceptionHandling, cUnit->numBlocks++);
    dvmInsertGrowableList(&cUnit->blockList, (intptr_t) bb);
    cUnit->puntBlock = bb;

    cUnit->numDalvikRegisters = cUnit->method->registersSize;

    /* Verify if all blocks are connected as claimed */
    /* FIXME - to be disabled in the future */
    dvmCompilerDataFlowAnalysisDispatcher(cUnit, verifyPredInfo,
                                          kAllNodes,
                                          false /* isIterative */);


    /* Try to identify a loop */
    if (!dvmCompilerBuildLoop(cUnit))
        goto bail;

    dvmCompilerLoopOpt(cUnit);

    /*
     * Change the backward branch to the backward chaining cell after dataflow
     * analsys/optimizations are done.
     */
    dvmCompilerInsertBackwardChaining(cUnit);

    dvmCompilerInitializeRegAlloc(cUnit);

    /* Allocate Registers using simple local allocation scheme */
    dvmCompilerLocalRegAlloc(cUnit);

    /* Convert MIR to LIR, etc. */
    dvmCompilerMIR2LIR(cUnit);

    /* Loop contains never executed blocks / heavy instructions */
    if (cUnit->quitLoopMode) {
        if (cUnit->printMe || gDvmJit.receivedSIGUSR2) {
            ALOGD("Loop trace @ offset %04x aborted due to unresolved code info",
                 cUnit->entryBlock->startOffset);
        }
        goto bail;
    }

    /* Convert LIR into machine code. Loop for recoverable retries */
    do {
        dvmCompilerAssembleLIR(cUnit, info);
        cUnit->assemblerRetries++;
        if (cUnit->printMe && cUnit->assemblerStatus != kSuccess)
            ALOGD("Assembler abort #%d on %d", cUnit->assemblerRetries,
                  cUnit->assemblerStatus);
    } while (cUnit->assemblerStatus == kRetryAll);

    /* Loop is too big - bail out */
    if (cUnit->assemblerStatus == kRetryHalve) {
        goto bail;
    }

    if (cUnit->printMe || gDvmJit.receivedSIGUSR2) {
        ALOGD("Loop trace @ offset %04x", cUnit->entryBlock->startOffset);
        dvmCompilerCodegenDump(cUnit);
    }

    /*
     * If this trace uses class objects as constants,
     * dvmJitInstallClassObjectPointers will switch the thread state
     * to running and look up the class pointers using the descriptor/loader
     * tuple stored in the callsite info structure. We need to make this window
     * as short as possible since it is blocking GC.
     */
    if (cUnit->hasClassLiterals && info->codeAddress) {
        dvmJitInstallClassObjectPointers(cUnit, (char *) info->codeAddress);
    }

    /*
     * Since callsiteinfo is allocated from the arena, delay the reset until
     * class pointers are resolved.
     */
    dvmCompilerArenaReset();

    assert(cUnit->assemblerStatus == kSuccess);
#if defined(WITH_JIT_TUNING)
    /* Locate the entry to store compilation statistics for this method */
    methodStats = dvmCompilerAnalyzeMethodBody(desc->method, false);
    methodStats->nativeSize += cUnit->totalSize;
#endif
    return info->codeAddress != NULL;

bail:
    /* Retry the original trace with JIT_OPT_NO_LOOP disabled */
    dvmCompilerArenaReset();
    return dvmCompileTrace(desc, numMaxInsts, info, bailPtr,
                           optHints | JIT_OPT_NO_LOOP);
}

void* runAddTest(void* regs)
{
    //int* registers = regs;
    //ALOGD("MGD EXECUTED OTHER FUNCTION: %X", registers[0]);
    return NULL;
}

void runOtherTest()
{
    u1* regs;
    __asm(

        "mov %[regs], r0\n\t"
        :[regs] "=r" (regs)
        :
        :"r0"
    );
    ALOGD("MGD EXECUTED OTHER FUNCTION: %X", regs[0]);
    
    return;
}

extern "C" void* hardcodeAdd(void* rgs)
{
    //ALOGD("MGD running HARDCODE ADD");

    /*
    u1* regs;
    __asm(

        "mov %[regs], r0\n\t"
        :[regs] "=r" (regs)
        :
        :"r0"
    );*/
    int* regs = (int*) rgs;
    //ALOGD("MGD REGS: %X - %d", (int)rgs, regs[0]);
    regs[0] = regs[2] + regs[3];
    //ALOGD("MGD Finished HARDCODE ADD");
    return NULL;
}

void hardcodeAdd2()
{

     ALOGD("MGD RAN HARDCODE ADD2");
     //return NULL;
}
//extern  ArmLIR *loadConstant(CompilationUnit*, int, int);
//extern  ArmLIR *opReg(CompilationUnit*, OpKind, int);
/*void buildStubTrace(CompilationUnit* cUnit, void** func)
{
    loadConstant(cUnit, 0, (int) *func);
    opReg(cUnit,kOpBlx,0 );
}*/


int traceprint = 10000;


typedef struct LLVMInsns {
    llvm::BasicBlock* label;
    LLVMInsns* next;
    LLVMInsns* prev;
    int id;

    void Init()
    {
        id = 0;
    }

    LLVMInsns* traverse(int i)
    {
        if(i>0) {
            if(next==NULL) {
                return this;
            }
            next->traverse(i-1);
        } else if(i<0) {
            if(prev==NULL) {
                return this;
            }
            prev->traverse(i+1);
        } else {
            return this;
        }
        return this;
    };

    LLVMInsns* add(llvm::BasicBlock* l)
    {
        next = new LLVMInsns();
        next->id = id+1;
        next->label = l;
        return next;
    }


} LLVMInsns;


bool dvmLLVMCompileTrace(JitTraceDescription *desc, int numMaxInsts,
                     JitTranslationInfo *info, jmp_buf *bailPtr,
                     int optHints, LLVMChaining& chaining)
{

    using namespace llvm;

        const bool debugprint = false;

    /////llvm::InitializeNativeTarget();
    //if(JitIsHere()){
            //ALOGD("LLVM - Entered my own JIT function");
    //if(strcmp(desc->method->name, "addTwo")!=0) {return false;}
    //info->codeAddress =(void*) (*runOtherTest);
    //ALOGD("MGD RETURNING STUFF");
    //return true;
    if(debugprint) // traceprint
        ALOGD("MGD LLVM TRACE HEAD %s : %s : %s", desc->method->name, desc->method->clazz->descriptor, desc->method->clazz->sourceFile);
    //ALOGD("MGD REGDATA DUMP: entry numbers: %d %d, FP: %X", desc->method->registerMap->numEntries[0], desc->method->registerMap->numEntries[1], *desc->method->insns);
    


    
   
 




    const DexCode *dexCode = dvmGetMethodCode(desc->method);
    const JitTraceRun* currRun = &desc->trace[0];
    unsigned int curOffset = currRun->info.frag.startOffset;
    //unsigned int startOffset = curOffset;
    unsigned int numInsts = currRun->info.frag.numInsts;
    const u2 *codePtr = dexCode->insns + curOffset;
    int traceSize = 0;  // # of half-words
    const u2 *startCodePtr = codePtr;
    //int numBlocks = 0;
    
    static int compilationId;
    CompilationUnit cUnit;
    //GrowableList *blockList;
#if defined(WITH_JIT_TUNING)
    CompilerMethodStats *methodStats;
#endif

    /* If we've already compiled this trace, just return success */
    if (dvmJitGetTraceAddr(startCodePtr) && !info->discardResult) {
        /*
         * Make sure the codeAddress is NULL so that it won't clobber the
         * existing entry.
         */
        info->codeAddress = NULL;
        return true;
    }

    /* If the work order is stale, discard it */
    if (info->cacheVersion != gDvmJit.cacheVersion) {
        return false;
    }

    compilationId++;
    memset(&cUnit, 0, sizeof(CompilationUnit));

#if defined(WITH_JIT_TUNING)
    /* Locate the entry to store compilation statistics for this method */
    methodStats = dvmCompilerAnalyzeMethodBody(desc->method, false);
#endif

    /* Set the recover buffer pointer */
    cUnit.bailPtr = bailPtr;

    /* Initialize the printMe flag */
    cUnit.printMe = gDvmJit.printMe;

    /* Setup the method */
    cUnit.method = desc->method;

    /* Store the trace descriptor and set the initial mode */
    cUnit.traceDesc = desc;
    cUnit.jitMode = kJitTrace;

    
	/*

	Create LLVM Module
	Set up compiler
	Create function prototype

	create basic block (for each instruction?)
	return instructions handled differently (to pass back dalvik pc of next trace)
	Compile trace
	return pointer to function & other necessary information
	*/
    /*
     * Analyze the trace descriptor and include up to the maximal number
     * of Dalvik instructions into the IR.
     */


 //}
    /*
    llvm::InitializeNativeTarget();

    llvm::Module* mod = new llvm::Module("LLVM Module", llvm::getGlobalContext());
    mod->setDataLayout("e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128-n8:16:32:64-S128");
    mod->setTargetTriple("armv7-unknown-linux-gnueabi");

    llvm::Constant* con = mod->getOrInsertFunction("test", llvm::IntegerType::get(mod->getContext(), 32), NULL);
    llvm::Function* testy = llvm::cast<llvm::Function>(con);
    llvm::BasicBlock* blk = llvm::BasicBlock::Create(llvm::getGlobalContext(), "ent", testy);
    llvm::IRBuilder<> b(blk);
    llvm::ConstantInt* const_int32_1 = llvm::ConstantInt::get(mod->getContext(), llvm::APInt(32, llvm::StringRef("5"), 10));
    b.CreateRet(const_int32_1);

    std::string errStr;
    llvm::ExecutionEngine* ee = llvm::EngineBuilder(mod).setErrorStr(&errStr).create();
    double calleeSave[8];
    int asmres = 10;
    int asmres2 = 10;

    ALOGD("LLVM Compiler - %s",errStr.c_str());
    llvm::Function* test = ee->FindFunctionNamed("test");
    void* asmptr = ee->getPointerToFunction(test);
  
    dvmJitCalleeSave(calleeSave);
  
    __asm(

        "blx  %0\n\t"
        "mov %[asmres], r0\n\t"
        "mov %[asmres2], r1\n\t"
        :[asmres] "=r" (asmres), [asmres2] "=r" (asmres2)
        :[asmptr] "r" (asmptr)
        : "r0", "r1"
    );

  
  dvmJitCalleeRestore(calleeSave);
  ALOGD("Assembly call result: %d , %d",asmres, asmres2);
    */
    const bool useBlocks = true;
    
    LLVMInsns* blockList = new LLVMInsns();
    blockList->Init();
    
    
    llvm::InitializeNativeTarget();
    llvm::Module * mod = new llvm::Module("JIT", llvm::getGlobalContext());
    mod->setDataLayout("e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128-n8:16:32:64-S128");
    mod->setTargetTriple("armv7-unknown-linux-gnueabi");
    // Type Definitions

    llvm::PointerType* IntegerPointer = llvm::PointerType::get(llvm::IntegerType::get(mod->getContext(), 32), 0);
    //llvm::PointerType* PointerToIntegerPointer = llvm::PointerType::get(IntegerPointer,0);
    //llvm::ArrayType* IntegerArray = llvm::ArrayType::get(llvm::IntegerType::get(mod->getContext(), 32), 5);
    //llvm::PointerType* PointerToIntegerArray = llvm::PointerType::get(IntegerArray, 0);



    llvm::Constant* con = mod->getOrInsertFunction("jitFunc",
                                    llvm::IntegerType::get(mod->getContext(), 32),
                                    llvm::PointerType::get(llvm::IntegerType::get(mod->getContext(), 32),0),
                                  NULL);
    llvm::Function* jitfunc = llvm::cast<llvm::Function>(con);
    jitfunc->setCallingConv(llvm::CallingConv::C);
    llvm::Function::arg_iterator args = jitfunc->arg_begin();
    llvm::Value* rgs = args++;
    rgs->setName("rgs");
    llvm::BasicBlock* main = llvm::BasicBlock::Create(mod->getContext(), "main", jitfunc, 0);
    llvm::BasicBlock* block = llvm::BasicBlock::Create(mod->getContext(), "BLOCK", jitfunc,0);
    llvm::BasicBlock* block2;
    llvm::BranchInst::Create(block, main);
    if(useBlocks) {
        blockList->label = block;
    }
    //llvm::IRBuilder<> builder(block);
    // set up arg handling
    llvm::AllocaInst* LLVMStack = new llvm::AllocaInst(IntegerPointer, "",block );
    LLVMStack->setAlignment(8);
    new llvm::StoreInst(rgs, LLVMStack, false, block);
    bool traceEnd = false;

     if(traceprint < 0) {return false;}
     traceprint -= 1;
    while (1) {
        MIR *insn;
        int width;
        insn = (MIR *)dvmCompilerNew(sizeof(MIR), true);
        insn->offset = curOffset;
        width = parseInsn(codePtr, &insn->dalvikInsn, cUnit.printMe);
	

        //====
        //const u2 *codePtrLLVM = dexCode->insns + curOffset;
        u2 inst = *codePtr;
        Opcode opcode = dexOpcodeFromCodeUnit(inst);
        opcodecount[(int)opcode] += 1;
        if(debugprint)
        ALOGD("MGD LLVM TRACE : %s, %d %d %d",
                                 dexGetOpcodeName(opcode),
                                insn->dalvikInsn.vA,
                                insn->dalvikInsn.vB,
                                insn->dalvikInsn.vC);
        
        
        if(opcode==OP_ADD_INT || opcode==OP_SUB_INT || opcode==OP_MUL_INT )
        {
            if(useBlocks) {
                blockList = blockList->add(block);
                block2 =  llvm::BasicBlock::Create(mod->getContext(), "INT", jitfunc,0);
                llvm::BranchInst::Create(block2, block);
                block = block2;
            }

			llvm::ConstantInt* vA = llvm::ConstantInt::get(mod->getContext(), llvm::APInt(32, insn->dalvikInsn.vA));
            llvm::ConstantInt* vB = llvm::ConstantInt::get(mod->getContext(), llvm::APInt(32, insn->dalvikInsn.vB));
            llvm::ConstantInt* vC = llvm::ConstantInt::get(mod->getContext(), llvm::APInt(32, insn->dalvikInsn.vC));
            llvm::LoadInst* LoadFromRegs = new llvm::LoadInst(LLVMStack,"",  false, block);
            llvm::GetElementPtrInst* OpA1 = llvm::GetElementPtrInst::Create(LoadFromRegs,vB, "", block);
            llvm::LoadInst* OpA2 = new llvm::LoadInst(OpA1, "", false, block);
            llvm::GetElementPtrInst* OpB1 = llvm::GetElementPtrInst::Create(LoadFromRegs, vC, "", block);
            llvm::LoadInst* OpB2 = new llvm::LoadInst(OpB1, "", false, block);
            //llvm::BinaryOperator* Result = llvm::BinaryOperator::Create(llvm::Instruction::Add, OpA2, OpB2, "", block);
            llvm::BinaryOperator* Result = NULL;
            if(opcode == OP_ADD_INT)
                    Result = llvm::BinaryOperator::Create(llvm::Instruction::Add, OpA2, OpB2, "", block);
                  

            if(opcode ==  OP_SUB_INT)
                    Result = llvm::BinaryOperator::Create(llvm::Instruction::Sub, OpA2, OpB2, "", block);
                   

            if(opcode ==  OP_MUL_INT)
                    Result = llvm::BinaryOperator::Create(llvm::Instruction::Mul, OpA2, OpB2, "", block);
         
                     
            llvm::GetElementPtrInst* ResultStore = llvm::GetElementPtrInst::Create(LoadFromRegs, vA, "", block);
            new llvm::StoreInst(Result, ResultStore, false, block);

            


        } else if (opcode==OP_NOP)
        {

        }
         else if(opcode==OP_ADD_INT_LIT8  || opcode==OP_MUL_INT_LIT8 )
        {
            if(useBlocks) {
                blockList = blockList->add(block);
                block2 =  llvm::BasicBlock::Create(mod->getContext(), "INT_LIT8", jitfunc,0);
                llvm::BranchInst::Create(block2, block);
                block = block2;
            }

            llvm::ConstantInt* vA = llvm::ConstantInt::get(mod->getContext(), llvm::APInt(32, insn->dalvikInsn.vA));
            llvm::ConstantInt* vB = llvm::ConstantInt::get(mod->getContext(), llvm::APInt(32, insn->dalvikInsn.vB));
            llvm::ConstantInt* vC = llvm::ConstantInt::get(mod->getContext(), llvm::APInt(32, insn->dalvikInsn.vC));
            llvm::LoadInst* LoadFromRegs = new llvm::LoadInst(LLVMStack,"",  false, block);
            llvm::GetElementPtrInst* OpA1 = llvm::GetElementPtrInst::Create(LoadFromRegs,vB, "", block);
            llvm::LoadInst* OpA2 = new llvm::LoadInst(OpA1, "", false, block);
            //llvm::GetElementPtrInst* OpB1 = llvm::GetElementPtrInst::Create(LoadFromRegs, vC, "", block);
            //llvm::LoadInst* OpB2 = new llvm::LoadInst(OpB1, "", false, block);
            //llvm::BinaryOperator* Result = llvm::BinaryOperator::Create(llvm::Instruction::Add, OpA2, OpB2, "", block);
            llvm::BinaryOperator* Result = NULL;
            if(opcode == OP_ADD_INT_LIT8)
                    Result = llvm::BinaryOperator::Create(llvm::Instruction::Add, OpA2, vC, "", block);
                  


            if(opcode ==  OP_MUL_INT_LIT8)
                    Result = llvm::BinaryOperator::Create(llvm::Instruction::Mul, OpA2, vC, "", block);
         
                     
            llvm::GetElementPtrInst* ResultStore = llvm::GetElementPtrInst::Create(LoadFromRegs, vA, "", block);
            new llvm::StoreInst(Result, ResultStore, false, block);

            


        }
         else if(opcode==OP_ADD_INT_2ADDR || opcode==OP_SUB_INT_2ADDR || opcode==OP_MUL_INT_2ADDR)
        {
            if(useBlocks) {
                blockList = blockList->add(block);
                block2 =  llvm::BasicBlock::Create(mod->getContext(), "INT-2ADDR", jitfunc,0);
                llvm::BranchInst::Create(block2, block);
                block = block2;
            }
            // Adds, subs or mulls vA with vB
            if(debugprint) ALOGD("LLVM ADDING 2ADDR instruction");
            llvm::ConstantInt* vA = llvm::ConstantInt::get(mod->getContext(), llvm::APInt(32, insn->dalvikInsn.vA));
            llvm::ConstantInt* vB = llvm::ConstantInt::get(mod->getContext(), llvm::APInt(32, insn->dalvikInsn.vB));
            
            llvm::LoadInst* LoadFromRegs = new llvm::LoadInst(LLVMStack,"",  false, block);
            llvm::GetElementPtrInst* OpA1 = llvm::GetElementPtrInst::Create(LoadFromRegs,vA, "", block);
            llvm::LoadInst* OpA2 = new llvm::LoadInst(OpA1, "", false, block);
            llvm::GetElementPtrInst* OpB1 = llvm::GetElementPtrInst::Create(LoadFromRegs, vB, "", block);
            llvm::LoadInst* OpB2 = new llvm::LoadInst(OpB1, "", false, block);

            llvm::BinaryOperator* Result = NULL;
            if(opcode == OP_ADD_INT_2ADDR)
                    Result = llvm::BinaryOperator::Create(llvm::Instruction::Add, OpA2, OpB2, "", block);
                  

            if(opcode ==  OP_SUB_INT_2ADDR)
                    Result = llvm::BinaryOperator::Create(llvm::Instruction::Sub, OpA2, OpB2, "", block);
                   

            if(opcode ==  OP_MUL_INT_2ADDR)
                    Result = llvm::BinaryOperator::Create(llvm::Instruction::Mul, OpA2, OpB2, "", block);
         
                     
            llvm::GetElementPtrInst* ResultStore = llvm::GetElementPtrInst::Create(LoadFromRegs, vA, "", block);
            new llvm::StoreInst(Result, ResultStore, false, block);
          
            
        }
        else if( opcode==OP_IF_EQZ || opcode==OP_IF_NEZ || opcode==OP_IF_LTZ || opcode==OP_IF_GEZ || opcode==OP_IF_GTZ || opcode==OP_IF_LEZ )
        {
            if(useBlocks) {
                blockList = blockList->add(block);
                block2 =  llvm::BasicBlock::Create(mod->getContext(), "IF", jitfunc,0);
                llvm::BranchInst::Create(block2, block);
                block = block2;
            }
            if(debugprint) ALOGD("LLVM ADDING IF-Z STATEMENT");

            // True Chaining Cell
            LLVMChainInfo chain;
            chain.num = chaining.num;
            chain.type = 1;
            chain.mir = insn;
            chaining.num+=1;
            chain.offset =  2*insn->dalvikInsn.vB + curOffset;
            llvm::ConstantInt* TrueChain = llvm::ConstantInt::get(mod->getContext(), APInt(32, chain.num));
            llvm::ConstantInt* FalseChain = llvm::ConstantInt::get(mod->getContext(), APInt(32, chain.num+1));
            //ALOGD("LLVM IF DEBUG: INTS");
            llvm::BasicBlock* TrueBranch = llvm::BasicBlock::Create(mod->getContext(), "TRUEBRANCH", jitfunc);
            llvm::BasicBlock* FalseBranch = llvm::BasicBlock::Create(mod->getContext(), "FALSEBRANCH", jitfunc);
            //llvm::BasicBlock* FallThrough = llvm::BasicBlock::Create(mod->getContext(), "", jitfunc);
            llvm::AllocaInst* rtnValue = new llvm::AllocaInst(llvm::IntegerType::get(mod->getContext(), 32), "", block);
            rtnValue->setAlignment(4);
            //llvm::AllocaInst* cmpValue = new llvm::AllocaInst(llvm::IntegerType::get(mod->getContext(), 32), "", block);
            //cmpValue->setAlignment(4);
            llvm::ConstantInt* constZero = llvm::ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10));
            llvm::ConstantInt* vA = llvm::ConstantInt::get(mod->getContext(), APInt(32, insn->dalvikInsn.vA));
            llvm::LoadInst* LoadFromRegs = new llvm::LoadInst(LLVMStack,"",  false, block);
            llvm::GetElementPtrInst* OpA1 = llvm::GetElementPtrInst::Create(LoadFromRegs,vA, "", block);
            llvm::LoadInst* OpA2 = new llvm::LoadInst(OpA1, "", false, block);
            llvm::ICmpInst* comparison;
            //ALOGD("LLVM IF DEBUG: COMPARISONS");
                //comparison = new llvm::ICmpInst(*block, llvm::ICmpInst::ICMP_SLT, OpA2, constZero, "");
            if(opcode==OP_IF_EQZ) {
                comparison = new llvm::ICmpInst(*block, llvm::ICmpInst::ICMP_EQ, OpA2, constZero, "IF_EQZ");
            }           
            else if(opcode==OP_IF_NEZ) {
                comparison = new llvm::ICmpInst(*block, llvm::ICmpInst::ICMP_NE, OpA2, constZero, "IF_NEZ");
            }         
            else if(opcode==OP_IF_LTZ) {
                comparison = new llvm::ICmpInst(*block, llvm::ICmpInst::ICMP_SLT, OpA2, constZero, "IF_LTZ");
            }       
            else if(opcode==OP_IF_GEZ) {
                comparison = new llvm::ICmpInst(*block, llvm::ICmpInst::ICMP_SGE, OpA2, constZero, "IF_GEZ");
            }
            else if(opcode==OP_IF_GTZ) {
                comparison = new llvm::ICmpInst(*block, llvm::ICmpInst::ICMP_SGT, OpA2, constZero, "IF_GTZ");
            }
            else if(opcode==OP_IF_LEZ) {
                comparison = new llvm::ICmpInst(*block, llvm::ICmpInst::ICMP_SLE, OpA2, constZero, "IF_LEZ");
            }    
            llvm::BranchInst::Create(TrueBranch, FalseBranch, comparison, block);

            // TrueBranch
            new llvm::StoreInst(TrueChain, rtnValue, false, TrueBranch);
            llvm::ReturnInst::Create(mod->getContext(), TrueChain, TrueBranch);
            

            // FalseBranch
            new llvm::StoreInst(FalseChain, rtnValue, false, FalseBranch);
            llvm::ReturnInst::Create(mod->getContext(), FalseChain, FalseBranch);
            
            chaining.chains.push_back(chain);

            // False chaining cell
            LLVMChainInfo chain2;
            chain2.num = chaining.num;
            chain2.type = 1;
            chain2.mir = insn;
            chaining.num +=1;
            chain2.offset = curOffset + width;
            chaining.chains.push_back(chain2);


            traceEnd = true;

            
        } else if (opcode==OP_IF_EQ || opcode==OP_IF_NE || opcode==OP_IF_LT || opcode==OP_IF_GE || opcode==OP_IF_GT || opcode==OP_IF_LE)
        {
            if(useBlocks) {
                blockList = blockList->add(block);
                block2 =  llvm::BasicBlock::Create(mod->getContext(), "IF", jitfunc,0);
                llvm::BranchInst::Create(block2, block);
                block = block2;
            }
            if(debugprint) ALOGD("LLVM ADDING IF STATEMENT");

            // True Chaining Cell
            LLVMChainInfo chain;
            chain.num = chaining.num;
            chain.type = 1;
            chain.mir = insn;
            chaining.num+=1;
            chain.offset =  2*insn->dalvikInsn.vC + curOffset;
            llvm::ConstantInt* TrueChain = llvm::ConstantInt::get(mod->getContext(), APInt(32, chain.num));
            llvm::ConstantInt* FalseChain = llvm::ConstantInt::get(mod->getContext(), APInt(32, chain.num+1));
            //ALOGD("LLVM IF DEBUG: INTS");
            llvm::BasicBlock* TrueBranch = llvm::BasicBlock::Create(mod->getContext(), "TRUEBRANCH", jitfunc);
            llvm::BasicBlock* FalseBranch = llvm::BasicBlock::Create(mod->getContext(), "FALSEBRANCH", jitfunc);
            //llvm::BasicBlock* FallThrough = llvm::BasicBlock::Create(mod->getContext(), "", jitfunc);
            llvm::AllocaInst* rtnValue = new llvm::AllocaInst(llvm::IntegerType::get(mod->getContext(), 32), "", block);
            rtnValue->setAlignment(4);
            //llvm::AllocaInst* cmpValue = new llvm::AllocaInst(llvm::IntegerType::get(mod->getContext(), 32), "", block);
            //cmpValue->setAlignment(4);
            llvm::ConstantInt* vB = llvm::ConstantInt::get(mod->getContext(), APInt(32, insn->dalvikInsn.vB));
            llvm::ConstantInt* vA = llvm::ConstantInt::get(mod->getContext(), APInt(32, insn->dalvikInsn.vA));

            llvm::LoadInst* LoadFromRegs = new llvm::LoadInst(LLVMStack,"",  false, block);
            llvm::GetElementPtrInst* OpA1 = llvm::GetElementPtrInst::Create(LoadFromRegs,vA, "", block);
            llvm::LoadInst* OpA2 = new llvm::LoadInst(OpA1, "", false, block);

            llvm::GetElementPtrInst* OpB1 = llvm::GetElementPtrInst::Create(LoadFromRegs,vB, "", block);
            llvm::LoadInst* OpB2= new llvm::LoadInst(OpB1, "", false, block);

            llvm::ICmpInst* comparison;
            //ALOGD("LLVM IF DEBUG: COMPARISONS");
                //comparison = new llvm::ICmpInst(*block, llvm::ICmpInst::ICMP_SLT, OpA2, OpB2, "");
            if(opcode==OP_IF_EQ) {
                comparison = new llvm::ICmpInst(*block, llvm::ICmpInst::ICMP_EQ, OpA2, OpB2, "IF_EQ");
            }           
            else if(opcode==OP_IF_NE) {
                comparison = new llvm::ICmpInst(*block, llvm::ICmpInst::ICMP_NE, OpA2, OpB2, "IF_NE");
            }         
            else if(opcode==OP_IF_LT) {
                comparison = new llvm::ICmpInst(*block, llvm::ICmpInst::ICMP_SLT, OpA2, OpB2, "IF_LT");
            }       
            else if(opcode==OP_IF_GE) {
                comparison = new llvm::ICmpInst(*block, llvm::ICmpInst::ICMP_SGE, OpA2, OpB2, "IF_GE");
            }
            else if(opcode==OP_IF_GT) {
                comparison = new llvm::ICmpInst(*block, llvm::ICmpInst::ICMP_SGT, OpA2, OpB2, "IF_GT");
            }
            else if(opcode==OP_IF_LE) {
                comparison = new llvm::ICmpInst(*block, llvm::ICmpInst::ICMP_SLE, OpA2, OpB2, "IF_LE");
            }    
            //ALOGD("LLVM IF DEBUG: BRANCHES");
            llvm::BranchInst::Create(TrueBranch, FalseBranch, comparison, block);

            // TrueBranch
            new llvm::StoreInst(TrueChain, rtnValue, false, TrueBranch);
            llvm::ReturnInst::Create(mod->getContext(), TrueChain, TrueBranch);
            

            // FalseBranch
            new llvm::StoreInst(FalseChain, rtnValue, false, FalseBranch);
            llvm::ReturnInst::Create(mod->getContext(), FalseChain, FalseBranch);
            //ALOGD("LLVM IF DEBUG: BLOCKLIST");
            
            chaining.chains.push_back(chain);

            //ALOGD("LLVM IF DEBUG: CHAINING");
            // False chaining cell
            LLVMChainInfo chain2;
            chain2.num = chaining.num;
            chain2.type = 1;
            chain2.mir = insn;
            chaining.num +=1;
            chain2.offset = curOffset + width;
            chaining.chains.push_back(chain2);


            traceEnd = true;
        } else if (opcode==OP_CONST_4)// || opcode==OP_CONST_16 || opcode==OP_CONST)
        {
            if(debugprint) ALOGD("LLVM BAILING ON CONST, broken");
            return false;
            
            if(debugprint) ALOGD("LLVM ADDING CONST_4");
            // regs[vA] = vB
            llvm::ConstantInt* vA = llvm::ConstantInt::get(mod->getContext(), llvm::APInt(32, insn->dalvikInsn.vA));
            
            llvm::LoadInst* LoadFromRegs = new llvm::LoadInst(LLVMStack,"",  false, block);

            llvm::ConstantInt* Mask  = llvm::ConstantInt::get(mod->getContext(), llvm::APInt(32, 255));
            llvm::ConstantInt* Shift = llvm::ConstantInt::get(mod->getContext(), llvm::APInt(32, 4));

            ///llvm::Value highBits;
            ///llvm::Value lowBits;
            llvm::GetElementPtrInst* OpA1 = llvm::GetElementPtrInst::Create(LoadFromRegs,vA, "", block);
            llvm::LoadInst* OpA2 = new llvm::LoadInst(OpA1, "", false, block);
            llvm::Value* highBits = BinaryOperator::Create(Instruction::LShr, OpA2, Shift, "", block);
            llvm::Value* lowBits = BinaryOperator::Create(Instruction::And, OpA2, Mask, "", block);
            llvm::CastInst* Dest = new llvm::ZExtInst(lowBits, IntegerType::get(mod->getContext(), 64), "", block);
            llvm::GetElementPtrInst* ResultStore = llvm::GetElementPtrInst::Create(LoadFromRegs, Dest, "", block);

            llvm::StoreInst(highBits, ResultStore, false, block); // Backtrace points to here for crash

            //new llvm::StoreInst(vB, OpA1, false, block);


        } else if (opcode==OP_CONST_16 )// || opcode==OP_CONST_16 || opcode==OP_CONST)
        {
            //return false;
            if(debugprint) ALOGD("LLVM ADDING CONST");
            // regs[vA] = vB
            llvm::ConstantInt* vA = llvm::ConstantInt::get(mod->getContext(), llvm::APInt(32, insn->dalvikInsn.vA));
            llvm::ConstantInt* vB = llvm::ConstantInt::get(mod->getContext(), llvm::APInt(32, insn->dalvikInsn.vB));
            
            llvm::LoadInst* LoadFromRegs = new llvm::LoadInst(LLVMStack,"",  false, block);

            llvm::GetElementPtrInst* ResultStore = llvm::GetElementPtrInst::Create(LoadFromRegs, vA, "", block);
            new llvm::StoreInst(vB, ResultStore, false, block);
            //new llvm::StoreInst(vB, OpA1, false, block);


        }
        else if(opcode==OP_RETURN)
        {

            if(debugprint) ALOGD("LLVM ADDING RETURN");
            LLVMChainInfo chain;
            chain.num = chaining.num;
            chain.type = 0;
            chain.mir = insn;
            chaining.num += 1;
            llvm::ConstantInt* toChain = ConstantInt::get(mod->getContext(), APInt(32, chain.num));
            llvm::ReturnInst::Create(mod->getContext(), toChain, block);
            chaining.chains.push_back(chain);
            if(debugprint) ALOGD("LLVM RETURN DEBUG: BLOCKLIST");
            //blockList = blockList->add(block);
            //block2 =  llvm::BasicBlock::Create(mod->getContext(), "RETURN", jitfunc,0);
            //llvm::BranchInst::Create(block2, block);
            //block = block2;
            if(debugprint) ALOGD("LLVM RETURN DEBUG: DONE");
            traceEnd =  true;
        }
        else if (opcode==OP_GOTO) {
            return false;
            if(debugprint) ALOGD("LLVM ADDING GOTO");
            LLVMChainInfo chain;
            chain.num = chaining.num;
            chain.type = 2;
            chain.mir = insn;
            chaining.num+=1;
            chain.offset = insn->dalvikInsn.vA*2 + curOffset - 2;
            chaining.chains.push_back(chain);
            llvm::ConstantInt* toChain = ConstantInt::get(mod->getContext(), APInt(32, chain.num));
            llvm::ReturnInst::Create(mod->getContext(), toChain, block);
            traceEnd = true;

            //blockList = blockList->add(block);
            //block2 =  llvm::BasicBlock::Create(mod->getContext(), "GOTO", jitfunc,0);
            //llvm::BranchInst::Create(block2, block);
            //block = block2;


            //llvm::BranchInst::Create(blockList->traverse(insn->dalvikInsn.vA)->label, block);

            
        }
        else if(opcode==OP_MOVE ) {
            if(debugprint) ALOGD("LLVM ADDING OP_MOVE");
            llvm::ConstantInt* vA = llvm::ConstantInt::get(mod->getContext(), llvm::APInt(32, insn->dalvikInsn.vA));
            llvm::ConstantInt* vB = llvm::ConstantInt::get(mod->getContext(), llvm::APInt(32, insn->dalvikInsn.vB));
            
            llvm::LoadInst* LoadFromRegs = new llvm::LoadInst(LLVMStack,"",  false, block);
            llvm::GetElementPtrInst* OpA1 = llvm::GetElementPtrInst::Create(LoadFromRegs,vA, "", block);
            llvm::LoadInst* OpA2 = new llvm::LoadInst(OpA1, "", false, block);
            llvm::GetElementPtrInst* OpB1 = llvm::GetElementPtrInst::Create(LoadFromRegs, vB, "", block);
            llvm::LoadInst* OpB2 = new llvm::LoadInst(OpB1, "", false, block);


            new llvm::StoreInst(OpA2, OpB1, false, block);
            new llvm::StoreInst(OpB2, OpA1, false, block);

        } else if(opcode==OP_AGET) {
            // vA = vB[vC*4];
            if(debugprint) ALOGD("BAILING ON OP_AGET");
            return false;
            //ALOGD("LLVM ADDING OP_AGET");
            //ALOGD("LLVM AGET START");
            PointerType* PointerTy_1 = PointerType::get(IntegerType::get(mod->getContext(), 32), 0);
            llvm::ConstantInt* vA = llvm::ConstantInt::get(mod->getContext(), llvm::APInt(32, insn->dalvikInsn.vA));
            llvm::ConstantInt* vB = llvm::ConstantInt::get(mod->getContext(), llvm::APInt(32, insn->dalvikInsn.vB));
            llvm::ConstantInt* vC = llvm::ConstantInt::get(mod->getContext(), llvm::APInt(32, insn->dalvikInsn.vC));
            llvm::LoadInst* LoadFromRegs = new llvm::LoadInst(LLVMStack,"",  false, block);
           // ALOGD("LLVM AGET REGS");
            ////llvm::GetElementPtrInst* OpA1 = llvm::GetElementPtrInst::Create(LoadFromRegs,vA, "", block);
            ////llvm::LoadInst* OpA2 = new llvm::LoadInst(OpA1, "", false, block);
            llvm::GetElementPtrInst* OpC1 = llvm::GetElementPtrInst::Create(LoadFromRegs, vC, "", block);
            llvm::LoadInst* OpC2 = new llvm::LoadInst(OpC1, "", false, block);

            llvm::GetElementPtrInst* OpB1 = llvm::GetElementPtrInst::Create(LoadFromRegs, vB, "", block);
            llvm::LoadInst* OpB2 = new llvm::LoadInst(OpB1, "", false, block);
            


            AllocaInst* ptr_arr = new AllocaInst(PointerTy_1, "arr", block);
            ptr_arr->setAlignment(8);

            GetElementPtrInst* ptr_20 = GetElementPtrInst::Create(LoadFromRegs, OpB2, "", block);
            new StoreInst(ptr_20, ptr_arr, false, block);
            GetElementPtrInst* ptr_25 = GetElementPtrInst::Create(ptr_20, OpC2, "", block);
            LoadInst* Result = new LoadInst(ptr_25, "", false, block);




            ////new llvm::StoreInst(OpA2, OpG2, false, block);
            //ALOGD("LLVM AGET STORE");
             llvm::GetElementPtrInst* ResultStore = llvm::GetElementPtrInst::Create(LoadFromRegs, vA, "", block);
            new llvm::StoreInst(Result, ResultStore, false, block);

        }
        else
        {
            // unrecognised instruciton
            if(debugprint) ALOGD("LLVM BAILING UNIMPLEMENTED OP : %s", dexGetOpcodeName(opcode));
            return false;
        }
        if(traceEnd)
        {
            llvm::PassManager PM;
            std::string msg;

            if(debugprint) ALOGD("LLVM DEBUG: PRINTING");
            llvm::raw_string_ostream mystream(msg);
            PM.add(llvm::createPrintModulePass(&mystream));
            PM.run(*mod);
            std::istringstream stream(msg);
            std::string line;
            if(debugprint) ALOGD("LLVM OUTPUT IR BEFORE OPTIMISATION ====================================");
            while(std::getline(stream, line)) {
                if(debugprint) ALOGD("%s", line.c_str());
            }
                            //ALOGD("LLVM OUTPUT : %s", msg.c_str());
            std::string verMsg;
            if(debugprint) ALOGD("LLVM DEBUG: Verify");
            if(llvm::verifyModule(*mod, llvm::PrintMessageAction, &verMsg)) {
                if(debugprint) ALOGD("LLVM INVALID MODULE: %s", verMsg.c_str());
            } else {
                if(debugprint) ALOGD("LLVM VERTIFY MESSAGE: %s", verMsg.c_str());
            }
            bool optimise = true;
            if(optimise) {
                if(debugprint) ALOGD("LLVM ATTEMPTING TO DO LOADS OF PASSES");
                // Add in optimizations. These were taken from a list that 'opt', LLVMs optimization tool, uses.
                llvm::PassManager p;
                p.add(llvm::createLintPass());
                p.add(llvm::createPromoteMemoryToRegisterPass());
                p.add(llvm::createConstantMergePass());
                p.add(llvm::createConstantPropagationPass());
                p.add(llvm::createDeadArgEliminationPass());
                p.add(llvm::createDeadCodeEliminationPass());
                p.add(llvm::createDeadInstEliminationPass());
                p.add(llvm::createDeadStoreEliminationPass());
                p.add(llvm::createCFGSimplificationPass());
                p.add(llvm::createPromoteMemoryToRegisterPass());
                p.add(llvm::createGlobalDCEPass());
                //p.add(llvm::createFunctionInliningPass()); 
                //p.add(llvm::createDemoteRegisterToMemoryPass());
                p.add(llvm::createGlobalOptimizerPass());
                p.add(llvm::createGlobalsModRefPass());
                p.add(llvm::createIPConstantPropagationPass());
                //p.add(llvm::createIPSCCPPass());
                p.add(llvm::createIndVarSimplifyPass());
                p.add(llvm::createInstructionCombiningPass());
                p.add(llvm::createLCSSAPass());
                p.add(llvm::createLICMPass());
                p.add(llvm::createLazyValueInfoPass());
                p.add(llvm::createLoopExtractorPass());
                p.add(llvm::createLoopSimplifyPass());
                p.add(llvm::createLoopStrengthReducePass());
                p.add(llvm::createLoopUnrollPass());
                p.add(llvm::createLoopUnswitchPass());
                p.add(llvm::createLoopIdiomPass());



                /*
                //p.add(new llvm::TargetData(jit));
                //p.add(llvm::createVerifierPass());
                //p.add(llvm::createLowerSetJmpPass());
                //p.add(llvm::createRaiseAllocationsPass());
                p.add(llvm::createCFGSimplificationPass());
                p.add(llvm::createPromoteMemoryToRegisterPass());
                p.add(llvm::createGlobalOptimizerPass());
                p.add(llvm::createGlobalDCEPass());
                p.add(llvm::createFunctionInliningPass()); 

                p.add(llvm::createAAEvalPass());
                p.add(llvm::createAggressiveDCEPass());
                p.add(llvm::createAliasAnalysisCounterPass());
                p.add(llvm::createAliasDebugger());
                p.add(llvm::createArgumentPromotionPass());
                p.add(llvm::createBasicAliasAnalysisPass());
                p.add(llvm::createLibCallAliasAnalysisPass(0));
                p.add(llvm::createScalarEvolutionAliasAnalysisPass());
                p.add(llvm::createTypeBasedAliasAnalysisPass());
                p.add(llvm::createBlockPlacementPass());
                p.add(llvm::createBoundsCheckingPass());
                p.add(llvm::createBreakCriticalEdgesPass());
               
                p.add(llvm::createCFGSimplificationPass());
                p.add(llvm::createConstantMergePass());
                p.add(llvm::createConstantPropagationPass());
                p.add(llvm::createDeadArgEliminationPass());
                p.add(llvm::createDeadCodeEliminationPass());
                p.add(llvm::createDeadInstEliminationPass());
                p.add(llvm::createDeadStoreEliminationPass());
             //   p.add(llvm::createDomOnlyPrinterPass());
             //   p.add(llvm::createDomPrinterPass());
                p.add(llvm::createDomOnlyViewerPass());
                p.add(llvm::createDomViewerPass());
                p.add(llvm::createEdgeProfilerPass());
                p.add(llvm::createOptimalEdgeProfilerPass());
                p.add(llvm::createPathProfilerPass());
                p.add(llvm::createGCOVProfilerPass());
                p.add(llvm::createFunctionInliningPass());
                p.add(llvm::createAlwaysInlinerPass());
                p.add(llvm::createGlobalDCEPass());
                p.add(llvm::createGlobalOptimizerPass());
                p.add(llvm::createGlobalsModRefPass());
                p.add(llvm::createIPConstantPropagationPass());
                p.add(llvm::createIPSCCPPass());
                p.add(llvm::createIndVarSimplifyPass());
                p.add(llvm::createInstructionCombiningPass());
                p.add(llvm::createLCSSAPass());
                p.add(llvm::createLICMPass());
                p.add(llvm::createLazyValueInfoPass());
                p.add(llvm::createLoopExtractorPass());
                p.add(llvm::createLoopSimplifyPass());
                p.add(llvm::createLoopStrengthReducePass());
                p.add(llvm::createLoopUnrollPass());
                p.add(llvm::createLoopUnswitchPass());
                p.add(llvm::createLoopIdiomPass());
                p.add(llvm::createLoopRotatePass());
                p.add(llvm::createLowerExpectIntrinsicPass());
                p.add(llvm::createLowerInvokePass());
                p.add(llvm::createLowerSwitchPass());
                p.add(llvm::createNoAAPass());
                p.add(llvm::createNoProfileInfoPass());
                p.add(llvm::createObjCARCAliasAnalysisPass());
                p.add(llvm::createObjCARCAPElimPass());
                p.add(llvm::createObjCARCExpandPass());
                p.add(llvm::createObjCARCContractPass());
                p.add(llvm::createObjCARCOptPass());
                p.add(llvm::createProfileEstimatorPass());
                p.add(llvm::createProfileVerifierPass());
                p.add(llvm::createPathProfileVerifierPass());
                p.add(llvm::createProfileLoaderPass());
                p.add(llvm::createProfileMetadataLoaderPass());
                p.add(llvm::createPathProfileLoaderPass());
                p.add(llvm::createPromoteMemoryToRegisterPass());
                p.add(llvm::createDemoteRegisterToMemoryPass());
                p.add(llvm::createPruneEHPass());
               // p.add(llvm::createPostDomOnlyPrinterPass());
               // p.add(llvm::createPostDomPrinterPass());
                p.add(llvm::createPostDomOnlyViewerPass());
                p.add(llvm::createPostDomViewerPass());
                p.add(llvm::createReassociatePass());
                p.add(llvm::createRegionInfoPass());
              //  p.add(llvm::createRegionOnlyPrinterPass());
                p.add(llvm::createRegionOnlyViewerPass());
              //  p.add(llvm::createRegionPrinterPass());


              */
                /*
                p.add(llvm::createRegionViewerPass());
                p.add(llvm::createSCCPPass());
                p.add(llvm::createScalarReplAggregatesPass());
                p.add(llvm::createSimplifyLibCallsPass());
                p.add(llvm::createSingleLoopExtractorPass());
                p.add(llvm::createStripSymbolsPass());
                p.add(llvm::createStripNonDebugSymbolsPass());
                p.add(llvm::createStripDeadDebugInfoPass());
                p.add(llvm::createStripDeadPrototypesPass());
                p.add(llvm::createTailCallEliminationPass());
                p.add(llvm::createJumpThreadingPass());
                p.add(llvm::createUnifyFunctionExitNodesPass());
                p.add(llvm::createInstCountPass());
                p.add(llvm::createCodeGenPreparePass());
                p.add(llvm::createEarlyCSEPass());
                p.add(llvm::createGVNPass());
                p.add(llvm::createMemCpyOptPass());
                p.add(llvm::createLoopDeletionPass());
                p.add(llvm::createPostDomTree());
                p.add(llvm::createInstructionNamerPass());
                p.add(llvm::createFunctionAttrsPass());
                p.add(llvm::createMergeFunctionsPass());
             //   p.add(llvm::createModuleDebugInfoPrinterPass());
                p.add(llvm::createPartialInliningPass());
                
                p.add(llvm::createSinkingPass());
                p.add(llvm::createLowerAtomicPass());
                p.add(llvm::createCorrelatedValuePropagationPass());
             //   p.add(llvm::createMemDepPrinter());
                p.add(llvm::createInstructionSimplifierPass());
                p.add(llvm::createBBVectorizePass());



                */


                p.run(*mod);
            }
           
            if(debugprint) ALOGD("LLVM OUTPUT IR AFTER OPTIMISATION ====================================");
            llvm::PassManager PMa;
            std::string msga;
            llvm::raw_string_ostream mystreama(msga);
            PMa.add(llvm::createPrintModulePass(&mystreama));
            PMa.run(*mod);
            std::istringstream streama(msga);
            std::string linea;
            if(debugprint) ALOGD("LLVM OUTPUT IR");
            while(std::getline(streama, linea)) {
                if(debugprint) ALOGD("%s", linea.c_str());
            }

            //ALOGD("LLVM : %s", mystream.str().c_str());

            std::string errStr;
            llvm::ExecutionEngine* ee = llvm::EngineBuilder(mod).setErrorStr(&errStr).create();
            if(debugprint) ALOGD("LLVM Compiler - %s",errStr.c_str());
            //ALOGD("LLVM COMPILER chain to: %d", insn->dalvikInsn.vB + curOffset);
            llvm::Function* rtn = ee->FindFunctionNamed("jitFunc");
            if(debugprint) ALOGD("LLVM COMPILER GOT FUNCTION");
            llvm::MachineCodeInfo MCI;
            ee->runJITOnFunction(rtn, &MCI);
            ALOGD("LLVM JIT BENCH FUNCTION SIZE: %d bytes", MCI.size());
            void* funcptr = ee->getPointerToFunction(rtn);
            if(debugprint) ALOGD("LLVM COMPILER GOT POINTER");
            info->codeAddress = funcptr;
            return true;
        }
        /*
        switch(opcode)
        {
            case OP_NOP:
                break;
            case OP_ADD_INT:
            case OP_SUB_INT:
            case OP_MUL_INT:
            //case OP_DIV_INT:
                    llvm::ConstantInt* vA = llvm::ConstantInt::get(mod->getContext(), llvm::APInt(32, insn->dalvikInsn.vA));
                llvm::ConstantInt* vB = llvm::ConstantInt::get(mod->getContext(), llvm::APInt(32, insn->dalvikInsn.vB));
                llvm::ConstantInt* vC = llvm::ConstantInt::get(mod->getContext(), llvm::APInt(32, insn->dalvikInsn.vC));
                llvm::LoadInst* LoadFromRegs = new llvm::LoadInst(LLVMStack,"",  false, block);
                llvm::GetElementPtrInst* OpA1 = llvm::GetElementPtrInst::Create(LoadFromRegs,vB, "", block);
                llvm::LoadInst* OpA2 = new llvm::LoadInst(OpA1, "", false, block);
                llvm::GetElementPtrInst* OpB1 = llvm::GetElementPtrInst::Create(LoadFromRegs, vC, "", block);
                llvm::LoadInst* OpB2 = new llvm::LoadInst(OpB1, "", false, block);
                switch(opcode)
                {
                    case OP_ADD_INT:
                        llvm::BinaryOperator* Result = llvm::BinaryOperator::Create(llvm::Instruction::Add, OpA2, OpB2, "", block);
                        break;

                    case OP_SUB_INT:
                        llvm::BinaryOperator* Result = llvm::BinaryOperator::Create(llvm::Instruction::Sub, OpA2, OpB2, "", block);
                        break;

                    case OP_MUL_INT:
                        llvm::BinaryOperator* Result = llvm::BinaryOperator::Create(llvm::Instruction::Mul, OpA2, OpB2, "", block);
                        break;

                    case OP_DIV_INT:
                        //llvm::BinaryOperator* Result = llvm::BinaryOperator::Create(llvm::Instruction::Add, OpA2, OpB2, "", block);
                        break;
                    default:
                        break;
                }
                llvm::GetElementPtrInst* ResultStore = llvm::GetElementPtrInst::Create(LoadFromRegs, vA, "", block);
                new llvm::StoreInst(Result, ResultStore, false, block);
                break;
            case OP_IF_GEZ:
                LLVMChainInfo chain;
                chain.num = chaining.num;
                chaining.num+=1;
                chain.offset =  insn->dalvikInsn.vB + curOffset;
                //llvm::ConstantInt* vA = ConstantInt::get(mod->getContext(), APInt(32, insn->dalvikInsn.vA));
                llvm::ConstantInt* toChain = ConstantInt::get(mod->getContext(), APInt(32, chain.num));
                llvm::ReturnInst::Create(mod->getContext(), toChain, block);
                chaining.chains.push_back(chain);


                // BUILD

                std::string errStr;
                llvm::ExecutionEngine* ee = llvm::EngineBuilder(mod).setErrorStr(&errStr).create();
                ALOGD("LLVM Compiler - %s",errStr.c_str());
                ALOGD("LLVM COMPILER chain to: %d", insn->dalvikInsn.vB + curOffset);
                llvm::Function* rtn = ee->FindFunctionNamed("jitFunc");
                void* funcptr = ee->getPointerToFunction(rtn);
                info->codeAddress = funcptr;
                return true;
                break;
            default:
                //ALOGD("UNRECOGNISED : %d", (int)opcode)
                break;
        }*/
        //=====
	
	
        /* The trace should never incude instruction data */
        assert(width);
        insn->width = width;
        traceSize += width;
        //dvmCompilerAppendMIR(curBB, insn);
        cUnit.numInsts++;

        int flags = dexGetFlagsFromOpcode(insn->dalvikInsn.opcode);

        if (flags & kInstrInvoke) {
            const Method *calleeMethod = (const Method *)
                currRun[JIT_TRACE_CUR_METHOD].info.meta;
            assert(numInsts == 1);
            CallsiteInfo *callsiteInfo =
                (CallsiteInfo *)dvmCompilerNew(sizeof(CallsiteInfo), true);
            callsiteInfo->classDescriptor = (const char *)
                currRun[JIT_TRACE_CLASS_DESC].info.meta;
            callsiteInfo->classLoader = (Object *)
                currRun[JIT_TRACE_CLASS_LOADER].info.meta;
            callsiteInfo->method = calleeMethod;
            insn->meta.callsiteInfo = callsiteInfo;
        }

        /* Instruction limit reached - terminate the trace here */
        if (cUnit.numInsts >= numMaxInsts) {
            break;
        }
        if (--numInsts == 0) {
            if (currRun->info.frag.runEnd) {
                break;
            } else {
                /* Advance to the next trace description (ie non-meta info) */
                do {
                    currRun++;
                } while (!currRun->isCode);

                /* Dummy end-of-run marker seen */
                if (currRun->info.frag.numInsts == 0) {
                    break;
                }

               
                curOffset = currRun->info.frag.startOffset;
                numInsts = currRun->info.frag.numInsts;
                
                codePtr = dexCode->insns + curOffset;
            }
        } else {
            curOffset += width;
            codePtr += width;
        }
    }

    return false;
    //ALOGD("LLVM TRACE OP_ADD_INT: %d", opcodecount[144]);
    //ALOGD("LLVM FOR CURRENT TRACE:");
    for(int ops = 0; ops < 256; ops++)
    {
        if(opcodecount[ops] > 0) {
            //ALOGD("LLVM OPCODE: %X has count: %d", ops, opcodecount[ops]);
        }
        //opcodecount[ops] = 0;
    }
    
#if defined(WITH_JIT_TUNING)
    /* Convert # of half-word to bytes */
    methodStats->compiledDalvikSize += traceSize * 2;
#endif



    assert(cUnit.assemblerStatus == kSuccess);
#if defined(WITH_JIT_TUNING)
    methodStats->nativeSize += cUnit.totalSize;
#endif

    return info->codeAddress != NULL;
    
    /* ============================================================*/
    //return false;
}

/*
 * Main entry point to start trace compilation. Basic blocks are constructed
 * first and they will be passed to the codegen routines to convert Dalvik
 * bytecode into machine code.
 */

bool dvmCompileTrace(JitTraceDescription *desc, int numMaxInsts,
                     JitTranslationInfo *info, jmp_buf *bailPtr,
                     int optHints)
{

    const DexCode *dexCode = dvmGetMethodCode(desc->method);
    const JitTraceRun* currRun = &desc->trace[0];
    unsigned int curOffset = currRun->info.frag.startOffset;
    unsigned int startOffset = curOffset;
    unsigned int numInsts = currRun->info.frag.numInsts;
    const u2 *codePtr = dexCode->insns + curOffset;
    int traceSize = 0;  // # of half-words
    const u2 *startCodePtr = codePtr;
    BasicBlock *curBB, *entryCodeBB;
    int numBlocks = 0;
    static int compilationId;
    CompilationUnit cUnit;
    GrowableList *blockList;
#if defined(WITH_JIT_TUNING)
    CompilerMethodStats *methodStats;
#endif

    /* If we've already compiled this trace, just return success */
    if (dvmJitGetTraceAddr(startCodePtr) && !info->discardResult) {
        /*
         * Make sure the codeAddress is NULL so that it won't clobber the
         * existing entry.
         */
        info->codeAddress = NULL;
        return true;
    }

    /* If the work order is stale, discard it */
    if (info->cacheVersion != gDvmJit.cacheVersion) {
        return false;
    }

    compilationId++;
    memset(&cUnit, 0, sizeof(CompilationUnit));



#if defined(WITH_JIT_TUNING)
    /* Locate the entry to store compilation statistics for this method */
    methodStats = dvmCompilerAnalyzeMethodBody(desc->method, false);
#endif

    /* Set the recover buffer pointer */
    cUnit.bailPtr = bailPtr;

    /* Initialize the printMe flag */
    cUnit.printMe = gDvmJit.printMe;

     if(strcmp(desc->method->name, "addTwo")==0){
        cUnit.printMe = true;
    }

    /* Setup the method */
    cUnit.method = desc->method;

    /* Store the trace descriptor and set the initial mode */
    cUnit.traceDesc = desc;
    cUnit.jitMode = kJitTrace;

    /* Initialize the PC reconstruction list */
    dvmInitGrowableList(&cUnit.pcReconstructionList, 8);

    /* Initialize the basic block list */
    blockList = &cUnit.blockList;
    dvmInitGrowableList(blockList, 8);

    /* Identify traces that we don't want to compile */
    if (gDvmJit.methodTable) {
        int len = strlen(desc->method->clazz->descriptor) +
                  strlen(desc->method->name) + 1;
        char *fullSignature = (char *)dvmCompilerNew(len, true);
        strcpy(fullSignature, desc->method->clazz->descriptor);
        strcat(fullSignature, desc->method->name);

        int hashValue = dvmComputeUtf8Hash(fullSignature);

        /*
         * Doing three levels of screening to see whether we want to skip
         * compiling this method
         */

        /* First, check the full "class;method" signature */
        bool methodFound =
            dvmHashTableLookup(gDvmJit.methodTable, hashValue,
                               fullSignature, (HashCompareFunc) strcmp,
                               false) !=
            NULL;

        /* Full signature not found - check the enclosing class */
        if (methodFound == false) {
            int hashValue = dvmComputeUtf8Hash(desc->method->clazz->descriptor);
            methodFound =
                dvmHashTableLookup(gDvmJit.methodTable, hashValue,
                               (char *) desc->method->clazz->descriptor,
                               (HashCompareFunc) strcmp, false) !=
                NULL;
            /* Enclosing class not found - check the method name */
            if (methodFound == false) {
                int hashValue = dvmComputeUtf8Hash(desc->method->name);
                methodFound =
                    dvmHashTableLookup(gDvmJit.methodTable, hashValue,
                                   (char *) desc->method->name,
                                   (HashCompareFunc) strcmp, false) !=
                    NULL;

                /*
                 * Debug by call-graph is enabled. Check if the debug list
                 * covers any methods on the VM stack.
                 */
                if (methodFound == false && gDvmJit.checkCallGraph == true) {
                    methodFound =
                        filterMethodByCallGraph(info->requestingThread,
                                                desc->method->name);
                }
            }
        }

        /*
         * Under the following conditions, the trace will be *conservatively*
         * compiled by only containing single-step instructions to and from the
         * interpreter.
         * 1) If includeSelectedMethod == false, the method matches the full or
         *    partial signature stored in the hash table.
         *
         * 2) If includeSelectedMethod == true, the method does not match the
         *    full and partial signature stored in the hash table.
         */
        if (gDvmJit.includeSelectedMethod != methodFound) {
            cUnit.allSingleStep = true;
        } else {
            /* Compile the trace as normal */

            /* Print the method we cherry picked */
            if (gDvmJit.includeSelectedMethod == true) {
                cUnit.printMe = true;
            }
        }
    }

    /* Allocate the entry block */
    curBB = dvmCompilerNewBB(kEntryBlock, numBlocks++);
    dvmInsertGrowableList(blockList, (intptr_t) curBB);
    curBB->startOffset = curOffset;

    entryCodeBB = dvmCompilerNewBB(kDalvikByteCode, numBlocks++);
    dvmInsertGrowableList(blockList, (intptr_t) entryCodeBB);
    entryCodeBB->startOffset = curOffset;
    curBB->fallThrough = entryCodeBB;
    curBB = entryCodeBB;

    if (cUnit.printMe) {
        ALOGD("--------\nCompiler: Building trace for %s, offset %#x",
             desc->method->name, curOffset);
    }

    /*
     * Analyze the trace descriptor and include up to the maximal number
     * of Dalvik instructions into the IR.
     */
    while (1) {
        MIR *insn;
        int width;
        insn = (MIR *)dvmCompilerNew(sizeof(MIR), true);
        insn->offset = curOffset;
        width = parseInsn(codePtr, &insn->dalvikInsn, cUnit.printMe);

        /* The trace should never incude instruction data */
        assert(width);
        insn->width = width;
        traceSize += width;
        dvmCompilerAppendMIR(curBB, insn);
        cUnit.numInsts++;

        int flags = dexGetFlagsFromOpcode(insn->dalvikInsn.opcode);

        if (flags & kInstrInvoke) {
            const Method *calleeMethod = (const Method *)
                currRun[JIT_TRACE_CUR_METHOD].info.meta;
            assert(numInsts == 1);
            CallsiteInfo *callsiteInfo =
                (CallsiteInfo *)dvmCompilerNew(sizeof(CallsiteInfo), true);
            callsiteInfo->classDescriptor = (const char *)
                currRun[JIT_TRACE_CLASS_DESC].info.meta;
            callsiteInfo->classLoader = (Object *)
                currRun[JIT_TRACE_CLASS_LOADER].info.meta;
            callsiteInfo->method = calleeMethod;
            insn->meta.callsiteInfo = callsiteInfo;
        }

        /* Instruction limit reached - terminate the trace here */
        if (cUnit.numInsts >= numMaxInsts) {
            break;
        }
        if (--numInsts == 0) {
            if (currRun->info.frag.runEnd) {
                break;
            } else {
                /* Advance to the next trace description (ie non-meta info) */
                do {
                    currRun++;
                } while (!currRun->isCode);

                /* Dummy end-of-run marker seen */
                if (currRun->info.frag.numInsts == 0) {
                    break;
                }

                curBB = dvmCompilerNewBB(kDalvikByteCode, numBlocks++);
                dvmInsertGrowableList(blockList, (intptr_t) curBB);
                curOffset = currRun->info.frag.startOffset;
                numInsts = currRun->info.frag.numInsts;
                curBB->startOffset = curOffset;
                codePtr = dexCode->insns + curOffset;
            }
        } else {
            curOffset += width;
            codePtr += width;
        }
    }

#if defined(WITH_JIT_TUNING)
    /* Convert # of half-word to bytes */
    methodStats->compiledDalvikSize += traceSize * 2;
#endif

    /*
     * Now scan basic blocks containing real code to connect the
     * taken/fallthrough links. Also create chaining cells for code not included
     * in the trace.
     */
    size_t blockId;
    for (blockId = 0; blockId < blockList->numUsed; blockId++) {
        curBB = (BasicBlock *) dvmGrowableListGetElement(blockList, blockId);
        MIR *lastInsn = curBB->lastMIRInsn;
        /* Skip empty blocks */
        if (lastInsn == NULL) {
            continue;
        }
        curOffset = lastInsn->offset;
        unsigned int targetOffset = curOffset;
        unsigned int fallThroughOffset = curOffset + lastInsn->width;
        bool isInvoke = false;
        const Method *callee = NULL;

        findBlockBoundary(desc->method, curBB->lastMIRInsn, curOffset,
                          &targetOffset, &isInvoke, &callee);

        /* Link the taken and fallthrough blocks */
        BasicBlock *searchBB;

        int flags = dexGetFlagsFromOpcode(lastInsn->dalvikInsn.opcode);

        if (flags & kInstrInvoke) {
            cUnit.hasInvoke = true;
        }

        /* Backward branch seen */
        if (isInvoke == false &&
            (flags & kInstrCanBranch) != 0 &&
            targetOffset < curOffset &&
            (optHints & JIT_OPT_NO_LOOP) == 0) {
            dvmCompilerArenaReset();
            return compileLoop(&cUnit, startOffset, desc, numMaxInsts,
                               info, bailPtr, optHints);
        }

        /* No backward branch in the trace - start searching the next BB */
        size_t searchBlockId;
        for (searchBlockId = blockId+1; searchBlockId < blockList->numUsed;
             searchBlockId++) {
            searchBB = (BasicBlock *) dvmGrowableListGetElement(blockList,
                                                                searchBlockId);
            if (targetOffset == searchBB->startOffset) {
                curBB->taken = searchBB;
                dvmCompilerSetBit(searchBB->predecessors, curBB->id);
            }
            if (fallThroughOffset == searchBB->startOffset) {
                curBB->fallThrough = searchBB;
                dvmCompilerSetBit(searchBB->predecessors, curBB->id);

                /*
                 * Fallthrough block of an invoke instruction needs to be
                 * aligned to 4-byte boundary (alignment instruction to be
                 * inserted later.
                 */
                if (flags & kInstrInvoke) {
                    searchBB->isFallThroughFromInvoke = true;
                }
            }
        }

        /*
         * Some blocks are ended by non-control-flow-change instructions,
         * currently only due to trace length constraint. In this case we need
         * to generate an explicit branch at the end of the block to jump to
         * the chaining cell.
         */
        curBB->needFallThroughBranch =
            ((flags & (kInstrCanBranch | kInstrCanSwitch | kInstrCanReturn |
                       kInstrInvoke)) == 0);
        if (lastInsn->dalvikInsn.opcode == OP_PACKED_SWITCH ||
            lastInsn->dalvikInsn.opcode == OP_SPARSE_SWITCH) {
            int i;
            const u2 *switchData = desc->method->insns + lastInsn->offset +
                             lastInsn->dalvikInsn.vB;
            int size = switchData[1];
            int maxChains = MIN(size, MAX_CHAINED_SWITCH_CASES);

            /*
             * Generate the landing pad for cases whose ranks are higher than
             * MAX_CHAINED_SWITCH_CASES. The code will re-enter the interpreter
             * through the NoChain point.
             */
            if (maxChains != size) {
                cUnit.switchOverflowPad =
                    desc->method->insns + lastInsn->offset;
            }

            s4 *targets = (s4 *) (switchData + 2 +
                    (lastInsn->dalvikInsn.opcode == OP_PACKED_SWITCH ?
                     2 : size * 2));

            /* One chaining cell for the first MAX_CHAINED_SWITCH_CASES cases */
            for (i = 0; i < maxChains; i++) {
                BasicBlock *caseChain = dvmCompilerNewBB(kChainingCellNormal,
                                                         numBlocks++);
                dvmInsertGrowableList(blockList, (intptr_t) caseChain);
                caseChain->startOffset = lastInsn->offset + targets[i];
            }

            /* One more chaining cell for the default case */
            BasicBlock *caseChain = dvmCompilerNewBB(kChainingCellNormal,
                                                     numBlocks++);
            dvmInsertGrowableList(blockList, (intptr_t) caseChain);
            caseChain->startOffset = lastInsn->offset + lastInsn->width;
        /* Fallthrough block not included in the trace */
        } else if (!isUnconditionalBranch(lastInsn) &&
                   curBB->fallThrough == NULL) {
            BasicBlock *fallThroughBB;
            /*
             * If the chaining cell is after an invoke or
             * instruction that cannot change the control flow, request a hot
             * chaining cell.
             */
            if (isInvoke || curBB->needFallThroughBranch) {
                fallThroughBB = dvmCompilerNewBB(kChainingCellHot, numBlocks++);
            } else {
                fallThroughBB = dvmCompilerNewBB(kChainingCellNormal,
                                                 numBlocks++);
            }
            dvmInsertGrowableList(blockList, (intptr_t) fallThroughBB);
            fallThroughBB->startOffset = fallThroughOffset;
            curBB->fallThrough = fallThroughBB;
            dvmCompilerSetBit(fallThroughBB->predecessors, curBB->id);
        }
        /* Target block not included in the trace */
        if (curBB->taken == NULL &&
            (isGoto(lastInsn) || isInvoke ||
            (targetOffset != UNKNOWN_TARGET && targetOffset != curOffset))) {
            BasicBlock *newBB = NULL;
            if (isInvoke) {
                /* Monomorphic callee */
                if (callee) {
                    /* JNI call doesn't need a chaining cell */
                    if (!dvmIsNativeMethod(callee)) {
                        newBB = dvmCompilerNewBB(kChainingCellInvokeSingleton,
                                                 numBlocks++);
                        newBB->startOffset = 0;
                        newBB->containingMethod = callee;
                    }
                /* Will resolve at runtime */
                } else {
                    newBB = dvmCompilerNewBB(kChainingCellInvokePredicted,
                                             numBlocks++);
                    newBB->startOffset = 0;
                }
            /* For unconditional branches, request a hot chaining cell */
            } else {
#if !defined(WITH_SELF_VERIFICATION)
                newBB = dvmCompilerNewBB(dexIsGoto(flags) ?
                                                  kChainingCellHot :
                                                  kChainingCellNormal,
                                         numBlocks++);
                newBB->startOffset = targetOffset;
#else
                /* Handle branches that branch back into the block */
                if (targetOffset >= curBB->firstMIRInsn->offset &&
                    targetOffset <= curBB->lastMIRInsn->offset) {
                    newBB = dvmCompilerNewBB(kChainingCellBackwardBranch,
                                             numBlocks++);
                } else {
                    newBB = dvmCompilerNewBB(dexIsGoto(flags) ?
                                                      kChainingCellHot :
                                                      kChainingCellNormal,
                                             numBlocks++);
                }
                newBB->startOffset = targetOffset;
#endif
            }
            if (newBB) {
                curBB->taken = newBB;
                dvmCompilerSetBit(newBB->predecessors, curBB->id);
                dvmInsertGrowableList(blockList, (intptr_t) newBB);
            }
        }
    }

    /* Now create a special block to host PC reconstruction code */
    curBB = dvmCompilerNewBB(kPCReconstruction, numBlocks++);
    dvmInsertGrowableList(blockList, (intptr_t) curBB);

    /* And one final block that publishes the PC and raise the exception */
    curBB = dvmCompilerNewBB(kExceptionHandling, numBlocks++);
    dvmInsertGrowableList(blockList, (intptr_t) curBB);
    cUnit.puntBlock = curBB;

    if (cUnit.printMe) {
        char* signature =
            dexProtoCopyMethodDescriptor(&desc->method->prototype);
        ALOGD("TRACEINFO (%d): 0x%08x %s%s.%s %#x %d of %d, %d blocks",
            compilationId,
            (intptr_t) desc->method->insns,
            desc->method->clazz->descriptor,
            desc->method->name,
            signature,
            desc->trace[0].info.frag.startOffset,
            traceSize,
            dexCode->insnsSize,
            numBlocks);
        free(signature);
    }

    cUnit.numBlocks = numBlocks;

    /* Set the instruction set to use (NOTE: later components may change it) */
    cUnit.instructionSet = dvmCompilerInstructionSet();

    /* Inline transformation @ the MIR level */
    if (cUnit.hasInvoke && !(gDvmJit.disableOpt & (1 << kMethodInlining))) {
        dvmCompilerInlineMIR(&cUnit, info);
    }

    cUnit.numDalvikRegisters = cUnit.method->registersSize;

    /* Preparation for SSA conversion */
    dvmInitializeSSAConversion(&cUnit);

    dvmCompilerNonLoopAnalysis(&cUnit);

    dvmCompilerInitializeRegAlloc(&cUnit);  // Needs to happen after SSA naming

    if (cUnit.printMe) {
        dvmCompilerDumpCompilationUnit(&cUnit);
    }

    /* Allocate Registers using simple local allocation scheme */
    dvmCompilerLocalRegAlloc(&cUnit);

    /* Convert MIR to LIR, etc. */
    dvmCompilerMIR2LIR(&cUnit);

    /* Convert LIR into machine code. Loop for recoverable retries */
    do {
        dvmCompilerAssembleLIR(&cUnit, info);
        std::string name = desc->method->name;
        std::string pre = "JIT";
        std::string pre2 = "LLVM";
        if(name.find(pre)!=std::string::npos) {
            ALOGD("BENCH STD JIT %s offset %d codesize: %d bytes",desc->method->name, currRun->info.frag.startOffset, cUnit.totalSize);
        }

         if(name.find(pre2)!=std::string::npos) {
            ALOGD("BENCH LLVM JIT %s offset %d codesize: %d bytes",desc->method->name, currRun->info.frag.startOffset, cUnit.totalSize);
        }

        cUnit.assemblerRetries++;
        if (cUnit.printMe && cUnit.assemblerStatus != kSuccess)
            ALOGD("Assembler abort #%d on %d",cUnit.assemblerRetries,
                  cUnit.assemblerStatus);
    } while (cUnit.assemblerStatus == kRetryAll);

    if (cUnit.printMe) {
        ALOGD("Trace Dalvik PC: %p", startCodePtr);
        dvmCompilerCodegenDump(&cUnit);
        ALOGD("End %s%s, %d Dalvik instructions",
             desc->method->clazz->descriptor, desc->method->name,
             cUnit.numInsts);
    }

    if (cUnit.assemblerStatus == kRetryHalve) {
        /* Reset the compiler resource pool before retry */
        dvmCompilerArenaReset();

        /* Halve the instruction count and start from the top */
        return dvmCompileTrace(desc, cUnit.numInsts / 2, info, bailPtr,
                               optHints);
    }

    /*
     * If this trace uses class objects as constants,
     * dvmJitInstallClassObjectPointers will switch the thread state
     * to running and look up the class pointers using the descriptor/loader
     * tuple stored in the callsite info structure. We need to make this window
     * as short as possible since it is blocking GC.
     */
    if (cUnit.hasClassLiterals && info->codeAddress) {
        dvmJitInstallClassObjectPointers(&cUnit, (char *) info->codeAddress);
    }

    /*
     * Since callsiteinfo is allocated from the arena, delay the reset until
     * class pointers are resolved.
     */
    dvmCompilerArenaReset();

    assert(cUnit.assemblerStatus == kSuccess);
#if defined(WITH_JIT_TUNING)
    methodStats->nativeSize += cUnit.totalSize;
#endif

    return info->codeAddress != NULL;
}
