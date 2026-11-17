module {
  handshake.func @histogram(%arg0: memref<1000xi32>, %arg1: memref<1000xf32>, %arg2: memref<1000xf32>, %arg3: !handshake.channel<i32>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["feature", "weight", "hist", "n", "feature_start", "weight_start", "hist_start", "start"], resNames = ["feature_end", "weight_end", "hist_end", "end"]} {
    %0:2 = lsq[%arg2 : memref<1000xf32>] (%arg6, %result, %addressResult_8, %addressResult_10, %dataResult_11, %result_18)  {groupSizes = [2 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.control<>)
    %outputs, %memEnd = mem_controller[%arg1 : memref<1000xf32>] %arg5 (%addressResult_6) %result_18 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %outputs_0, %memEnd_1 = mem_controller[%arg0 : memref<1000xi32>] %arg4 (%addressResult) %result_18 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %1 = constant %arg7 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = cmpi sgt, %arg3, %1 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %2, %1 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %2, %arg3 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %2, %arg7 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %3 = mux %index [%trueResult, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %4 = mux %index [%trueResult_2, %trueResult_14] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_4, %trueResult_16]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %6 = constant %5 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %7 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %8 = trunci %7 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%8] %outputs_0 {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %9 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %10 = trunci %9 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_6, %dataResult_7 = load[%10] %outputs {handshake.bb = 1 : ui32, handshake.name = "load1"} : <i32>, <f32>, <i32>, <f32>
    %11 = trunci %dataResult {handshake.bb = 1 : ui32, handshake.name = "index_cast2"} : <i32> to <i32>
    %addressResult_8, %dataResult_9 = load[%11] %0#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load2"} : <i32>, <f32>, <i32>, <f32>
    %12 = addf %dataResult_9, %dataResult_7 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "addf0"} : <f32>
    %13 = trunci %dataResult {handshake.bb = 1 : ui32, handshake.name = "index_cast3"} : <i32> to <i32>
    %addressResult_10, %dataResult_11 = store[%13] %12 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : <i32>, <f32>, <i32>, <f32>
    %14 = addi %3, %6 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %15 = cmpi slt, %14, %4 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %15, %14 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %15, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %15, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %result_18, %index_19 = control_merge [%falseResult_5, %falseResult_17]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %memEnd_1, %memEnd, %0#1, %arg7 : <>, <>, <>, <>
  }
}

