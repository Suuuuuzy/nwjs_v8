// Copyright 2015 the V8 project authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#include "src/compiler/backend/instruction-scheduler.h"

namespace v8 {
namespace internal {
namespace compiler {

bool InstructionScheduler::SchedulerSupported() { return true; }

int InstructionScheduler::GetTargetInstructionFlags(
    const Instruction* instr) const {
  switch (instr->arch_opcode()) {
    case kS390_Abs32:
    case kS390_Abs64:
    case kS390_And32:
    case kS390_And64:
    case kS390_Or32:
    case kS390_Or64:
    case kS390_Xor32:
    case kS390_Xor64:
    case kS390_ShiftLeft32:
    case kS390_ShiftLeft64:
    case kS390_ShiftRight32:
    case kS390_ShiftRight64:
    case kS390_ShiftRightArith32:
    case kS390_ShiftRightArith64:
    case kS390_RotRight32:
    case kS390_RotRight64:
    case kS390_Not32:
    case kS390_Not64:
    case kS390_RotLeftAndClear64:
    case kS390_RotLeftAndClearLeft64:
    case kS390_RotLeftAndClearRight64:
    case kS390_Lay:
    case kS390_Add32:
    case kS390_Add64:
    case kS390_AddFloat:
    case kS390_AddDouble:
    case kS390_Sub32:
    case kS390_Sub64:
    case kS390_SubFloat:
    case kS390_SubDouble:
    case kS390_Mul32:
    case kS390_Mul32WithOverflow:
    case kS390_Mul64:
    case kS390_MulHigh32:
    case kS390_MulHighU32:
    case kS390_MulFloat:
    case kS390_MulDouble:
    case kS390_Div32:
    case kS390_Div64:
    case kS390_DivU32:
    case kS390_DivU64:
    case kS390_DivFloat:
    case kS390_DivDouble:
    case kS390_Mod32:
    case kS390_Mod64:
    case kS390_ModU32:
    case kS390_ModU64:
    case kS390_ModDouble:
    case kS390_Neg32:
    case kS390_Neg64:
    case kS390_NegDouble:
    case kS390_NegFloat:
    case kS390_SqrtFloat:
    case kS390_FloorFloat:
    case kS390_CeilFloat:
    case kS390_TruncateFloat:
    case kS390_AbsFloat:
    case kS390_SqrtDouble:
    case kS390_FloorDouble:
    case kS390_CeilDouble:
    case kS390_TruncateDouble:
    case kS390_RoundDouble:
    case kS390_MaxFloat:
    case kS390_MaxDouble:
    case kS390_MinFloat:
    case kS390_MinDouble:
    case kS390_AbsDouble:
    case kS390_Cntlz32:
    case kS390_Cntlz64:
    case kS390_Popcnt32:
    case kS390_Popcnt64:
    case kS390_Cmp32:
    case kS390_Cmp64:
    case kS390_CmpFloat:
    case kS390_CmpDouble:
    case kS390_Tst32:
    case kS390_Tst64:
    case kS390_SignExtendWord8ToInt32:
    case kS390_SignExtendWord16ToInt32:
    case kS390_SignExtendWord8ToInt64:
    case kS390_SignExtendWord16ToInt64:
    case kS390_SignExtendWord32ToInt64:
    case kS390_Uint32ToUint64:
    case kS390_Int64ToInt32:
    case kS390_Int64ToFloat32:
    case kS390_Int64ToDouble:
    case kS390_Uint64ToFloat32:
    case kS390_Uint64ToDouble:
    case kS390_Int32ToFloat32:
    case kS390_Int32ToDouble:
    case kS390_Uint32ToFloat32:
    case kS390_Uint32ToDouble:
    case kS390_Float32ToInt32:
    case kS390_Float32ToUint32:
    case kS390_Float32ToUint64:
    case kS390_Float32ToDouble:
    case kS390_Float64SilenceNaN:
    case kS390_DoubleToInt32:
    case kS390_DoubleToUint32:
    case kS390_Float32ToInt64:
    case kS390_DoubleToInt64:
    case kS390_DoubleToUint64:
    case kS390_DoubleToFloat32:
    case kS390_DoubleExtractLowWord32:
    case kS390_DoubleExtractHighWord32:
    case kS390_DoubleInsertLowWord32:
    case kS390_DoubleInsertHighWord32:
    case kS390_DoubleConstruct:
    case kS390_BitcastInt32ToFloat32:
    case kS390_BitcastFloat32ToInt32:
    case kS390_BitcastInt64ToDouble:
    case kS390_BitcastDoubleToInt64:
    case kS390_LoadReverse16RR:
    case kS390_LoadReverse32RR:
    case kS390_LoadReverse64RR:
    case kS390_LoadReverseSimd128RR:
    case kS390_LoadReverseSimd128:
    case kS390_LoadAndTestWord32:
    case kS390_LoadAndTestWord64:
    case kS390_LoadAndTestFloat32:
    case kS390_LoadAndTestFloat64:
    case kS390_CompressSigned:
    case kS390_CompressPointer:
    case kS390_CompressAny:
    case kS390_F64x2Splat:
    case kS390_F64x2ReplaceLane:
    case kS390_F64x2Abs:
    case kS390_F64x2Neg:
    case kS390_F64x2Sqrt:
    case kS390_F64x2Add:
    case kS390_F64x2Sub:
    case kS390_F64x2Mul:
    case kS390_F64x2Div:
    case kS390_F64x2Eq:
    case kS390_F64x2Ne:
    case kS390_F64x2Lt:
    case kS390_F64x2Le:
    case kS390_F64x2Min:
    case kS390_F64x2Max:
    case kS390_F64x2ExtractLane:
    case kS390_F64x2Qfma:
    case kS390_F64x2Qfms:
    case kS390_F64x2Pmin:
    case kS390_F64x2Pmax:
    case kS390_F64x2Ceil:
    case kS390_F64x2Floor:
    case kS390_F64x2Trunc:
    case kS390_F64x2NearestInt:
    case kS390_F64x2ConvertLowI32x4S:
    case kS390_F64x2ConvertLowI32x4U:
    case kS390_F64x2PromoteLowF32x4:
    case kS390_F32x4Splat:
    case kS390_F32x4ExtractLane:
    case kS390_F32x4ReplaceLane:
    case kS390_F32x4Add:
    case kS390_F32x4AddHoriz:
    case kS390_F32x4Sub:
    case kS390_F32x4Mul:
    case kS390_F32x4Eq:
    case kS390_F32x4Ne:
    case kS390_F32x4Lt:
    case kS390_F32x4Le:
    case kS390_F32x4Abs:
    case kS390_F32x4Neg:
    case kS390_F32x4RecipApprox:
    case kS390_F32x4RecipSqrtApprox:
    case kS390_F32x4SConvertI32x4:
    case kS390_F32x4UConvertI32x4:
    case kS390_F32x4Sqrt:
    case kS390_F32x4Div:
    case kS390_F32x4Min:
    case kS390_F32x4Max:
    case kS390_F32x4Qfma:
    case kS390_F32x4Qfms:
    case kS390_F32x4Pmin:
    case kS390_F32x4Pmax:
    case kS390_F32x4Ceil:
    case kS390_F32x4Floor:
    case kS390_F32x4Trunc:
    case kS390_F32x4NearestInt:
    case kS390_F32x4DemoteF64x2Zero:
    case kS390_I64x2Neg:
    case kS390_I64x2Add:
    case kS390_I64x2Sub:
    case kS390_I64x2Shl:
    case kS390_I64x2ShrS:
    case kS390_I64x2ShrU:
    case kS390_I64x2Mul:
    case kS390_I64x2Splat:
    case kS390_I64x2ReplaceLane:
    case kS390_I64x2ExtractLane:
    case kS390_I64x2Eq:
    case kS390_I64x2BitMask:
    case kS390_I64x2ExtMulLowI32x4S:
    case kS390_I64x2ExtMulHighI32x4S:
    case kS390_I64x2ExtMulLowI32x4U:
    case kS390_I64x2ExtMulHighI32x4U:
    case kS390_I64x2SConvertI32x4Low:
    case kS390_I64x2SConvertI32x4High:
    case kS390_I64x2UConvertI32x4Low:
    case kS390_I64x2UConvertI32x4High:
    case kS390_I64x2SignSelect:
    case kS390_I64x2Ne:
    case kS390_I64x2GtS:
    case kS390_I64x2GeS:
    case kS390_I64x2Abs:
    case kS390_I32x4Splat:
    case kS390_I32x4ExtractLane:
    case kS390_I32x4ReplaceLane:
    case kS390_I32x4Add:
    case kS390_I32x4AddHoriz:
    case kS390_I32x4Sub:
    case kS390_I32x4Mul:
    case kS390_I32x4MinS:
    case kS390_I32x4MinU:
    case kS390_I32x4MaxS:
    case kS390_I32x4MaxU:
    case kS390_I32x4Eq:
    case kS390_I32x4Ne:
    case kS390_I32x4GtS:
    case kS390_I32x4GeS:
    case kS390_I32x4GtU:
    case kS390_I32x4GeU:
    case kS390_I32x4Shl:
    case kS390_I32x4ShrS:
    case kS390_I32x4ShrU:
    case kS390_I32x4Neg:
    case kS390_I32x4SConvertF32x4:
    case kS390_I32x4UConvertF32x4:
    case kS390_I32x4SConvertI16x8Low:
    case kS390_I32x4SConvertI16x8High:
    case kS390_I32x4UConvertI16x8Low:
    case kS390_I32x4UConvertI16x8High:
    case kS390_I32x4Abs:
    case kS390_I32x4BitMask:
    case kS390_I32x4DotI16x8S:
    case kS390_I32x4ExtMulLowI16x8S:
    case kS390_I32x4ExtMulHighI16x8S:
    case kS390_I32x4ExtMulLowI16x8U:
    case kS390_I32x4ExtMulHighI16x8U:
    case kS390_I32x4ExtAddPairwiseI16x8S:
    case kS390_I32x4ExtAddPairwiseI16x8U:
    case kS390_I32x4SignSelect:
    case kS390_I32x4TruncSatF64x2SZero:
    case kS390_I32x4TruncSatF64x2UZero:
    case kS390_I16x8Splat:
    case kS390_I16x8ExtractLaneU:
    case kS390_I16x8ExtractLaneS:
    case kS390_I16x8ReplaceLane:
    case kS390_I16x8Add:
    case kS390_I16x8AddHoriz:
    case kS390_I16x8Sub:
    case kS390_I16x8Mul:
    case kS390_I16x8MinS:
    case kS390_I16x8MinU:
    case kS390_I16x8MaxS:
    case kS390_I16x8MaxU:
    case kS390_I16x8Eq:
    case kS390_I16x8Ne:
    case kS390_I16x8GtS:
    case kS390_I16x8GeS:
    case kS390_I16x8GtU:
    case kS390_I16x8GeU:
    case kS390_I16x8Shl:
    case kS390_I16x8ShrS:
    case kS390_I16x8ShrU:
    case kS390_I16x8Neg:
    case kS390_I16x8SConvertI32x4:
    case kS390_I16x8UConvertI32x4:
    case kS390_I16x8SConvertI8x16Low:
    case kS390_I16x8SConvertI8x16High:
    case kS390_I16x8UConvertI8x16Low:
    case kS390_I16x8UConvertI8x16High:
    case kS390_I16x8AddSatS:
    case kS390_I16x8SubSatS:
    case kS390_I16x8AddSatU:
    case kS390_I16x8SubSatU:
    case kS390_I16x8RoundingAverageU:
    case kS390_I16x8Abs:
    case kS390_I16x8BitMask:
    case kS390_I16x8ExtMulLowI8x16S:
    case kS390_I16x8ExtMulHighI8x16S:
    case kS390_I16x8ExtMulLowI8x16U:
    case kS390_I16x8ExtMulHighI8x16U:
    case kS390_I16x8ExtAddPairwiseI8x16S:
    case kS390_I16x8ExtAddPairwiseI8x16U:
    case kS390_I16x8Q15MulRSatS:
    case kS390_I16x8SignSelect:
    case kS390_I8x16Splat:
    case kS390_I8x16ExtractLaneU:
    case kS390_I8x16ExtractLaneS:
    case kS390_I8x16ReplaceLane:
    case kS390_I8x16Add:
    case kS390_I8x16Sub:
    case kS390_I8x16Mul:
    case kS390_I8x16MinS:
    case kS390_I8x16MinU:
    case kS390_I8x16MaxS:
    case kS390_I8x16MaxU:
    case kS390_I8x16Eq:
    case kS390_I8x16Ne:
    case kS390_I8x16GtS:
    case kS390_I8x16GeS:
    case kS390_I8x16GtU:
    case kS390_I8x16GeU:
    case kS390_I8x16Shl:
    case kS390_I8x16ShrS:
    case kS390_I8x16ShrU:
    case kS390_I8x16Neg:
    case kS390_I8x16SConvertI16x8:
    case kS390_I8x16UConvertI16x8:
    case kS390_I8x16AddSatS:
    case kS390_I8x16SubSatS:
    case kS390_I8x16AddSatU:
    case kS390_I8x16SubSatU:
    case kS390_I8x16RoundingAverageU:
    case kS390_I8x16Abs:
    case kS390_I8x16BitMask:
    case kS390_I8x16Shuffle:
    case kS390_I8x16Swizzle:
    case kS390_I8x16SignSelect:
    case kS390_I8x16Popcnt:
    case kS390_V64x2AllTrue:
    case kS390_V32x4AllTrue:
    case kS390_V16x8AllTrue:
    case kS390_V8x16AllTrue:
    case kS390_V128AnyTrue:
    case kS390_S128And:
    case kS390_S128Or:
    case kS390_S128Xor:
    case kS390_S128Const:
    case kS390_S128Zero:
    case kS390_S128AllOnes:
    case kS390_S128Not:
    case kS390_S128Select:
    case kS390_S128AndNot:
      return kNoOpcodeFlags;

    case kS390_LoadWordS8:
    case kS390_LoadWordU8:
    case kS390_LoadWordS16:
    case kS390_LoadWordU16:
    case kS390_LoadWordS32:
    case kS390_LoadWordU32:
    case kS390_LoadWord64:
    case kS390_LoadFloat32:
    case kS390_LoadDouble:
    case kS390_LoadSimd128:
    case kS390_LoadReverse16:
    case kS390_LoadReverse32:
    case kS390_LoadReverse64:
    case kS390_Peek:
    case kS390_LoadDecompressTaggedSigned:
    case kS390_LoadDecompressTaggedPointer:
    case kS390_LoadDecompressAnyTagged:
      return kIsLoadOperation;

    case kS390_StoreWord8:
    case kS390_StoreWord16:
    case kS390_StoreWord32:
    case kS390_StoreWord64:
    case kS390_StoreReverseSimd128:
    case kS390_StoreReverse16:
    case kS390_StoreReverse32:
    case kS390_StoreReverse64:
    case kS390_StoreFloat32:
    case kS390_StoreDouble:
    case kS390_StoreSimd128:
    case kS390_StoreCompressTagged:
    case kS390_Push:
    case kS390_PushFrame:
    case kS390_StoreToStackSlot:
      return kHasSideEffect;

    case kS390_Word64AtomicExchangeUint8:
    case kS390_Word64AtomicExchangeUint16:
    case kS390_Word64AtomicExchangeUint32:
    case kS390_Word64AtomicExchangeUint64:
    case kS390_Word64AtomicCompareExchangeUint8:
    case kS390_Word64AtomicCompareExchangeUint16:
    case kS390_Word64AtomicCompareExchangeUint32:
    case kS390_Word64AtomicCompareExchangeUint64:
    case kS390_Word64AtomicAddUint8:
    case kS390_Word64AtomicAddUint16:
    case kS390_Word64AtomicAddUint32:
    case kS390_Word64AtomicAddUint64:
    case kS390_Word64AtomicSubUint8:
    case kS390_Word64AtomicSubUint16:
    case kS390_Word64AtomicSubUint32:
    case kS390_Word64AtomicSubUint64:
    case kS390_Word64AtomicAndUint8:
    case kS390_Word64AtomicAndUint16:
    case kS390_Word64AtomicAndUint32:
    case kS390_Word64AtomicAndUint64:
    case kS390_Word64AtomicOrUint8:
    case kS390_Word64AtomicOrUint16:
    case kS390_Word64AtomicOrUint32:
    case kS390_Word64AtomicOrUint64:
    case kS390_Word64AtomicXorUint8:
    case kS390_Word64AtomicXorUint16:
    case kS390_Word64AtomicXorUint32:
    case kS390_Word64AtomicXorUint64:
      return kHasSideEffect;

#define CASE(Name) case k##Name:
      COMMON_ARCH_OPCODE_LIST(CASE)
#undef CASE
      // Already covered in architecture independent code.
      UNREACHABLE();
  }

  UNREACHABLE();
}

int InstructionScheduler::GetInstructionLatency(const Instruction* instr) {
  // TODO(all): Add instruction cost modeling.
  return 1;
}

}  // namespace compiler
}  // namespace internal
}  // namespace v8
