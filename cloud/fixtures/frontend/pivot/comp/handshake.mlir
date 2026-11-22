module {
  handshake.func @pivot(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.channel<i32>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["x", "a", "n", "k", "x_start", "a_start", "start"], resNames = ["x_end", "a_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg1 : memref<1000xi32>] %arg5 (%addressResult_12) %result_26 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_0:2, %memEnd_1 = mem_controller[%arg0 : memref<1000xi32>] %arg4 (%6, %addressResult_14, %0#1, %0#2, %0#3) %result_26 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %0:4 = lsq[MC] (%result, %addressResult, %dataResult, %addressResult_10, %outputs_0#1)  {groupSizes = [2 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>)
    %1 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %2 = constant %1 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %3 = constant %arg6 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %4 = addi %arg3, %2 {handshake.bb = 0 : ui32, handshake.name = "addi0"} : <i32>
    %5 = cmpi slt, %arg3, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %5, %4 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %5, %3 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %5, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %5, %arg3 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %5, %arg6 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %6 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %7 = mux %index [%trueResult, %trueResult_16] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %8 = mux %index [%trueResult_2, %trueResult_18] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %9 = mux %index [%trueResult_4, %trueResult_20] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %10 = mux %index [%trueResult_6, %trueResult_22] {handshake.bb = 1 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_8, %trueResult_24]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %11 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %12 = constant %11 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %13 = trunci %10 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i32> to <i32>
    %addressResult, %dataResult = store[%13] %8 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store0"} : <i32>, <i32>, <i32>, <i32>
    %14 = trunci %10 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i32> to <i32>
    %addressResult_10, %dataResult_11 = load[%14] %0#0 {handshake.bb = 1 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %15 = trunci %7 {handshake.bb = 1 : ui32, handshake.name = "index_cast2"} : <i32> to <i32>
    %addressResult_12, %dataResult_13 = load[%15] %outputs {handshake.bb = 1 : ui32, handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    %16 = trunci %7 {handshake.bb = 1 : ui32, handshake.name = "index_cast3"} : <i32> to <i32>
    %addressResult_14, %dataResult_15 = load[%16] %outputs_0#0 {handshake.bb = 1 : ui32, handshake.name = "load3"} : <i32>, <i32>, <i32>, <i32>
    %17 = muli %dataResult_13, %dataResult_15 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %18 = subi %dataResult_11, %17 {handshake.bb = 1 : ui32, handshake.name = "subi0"} : <i32>
    %19 = addi %7, %12 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %20 = cmpi slt, %7, %9 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_16, %falseResult_17 = cond_br %20, %19 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %20, %18 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %20, %9 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %20, %10 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %20, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %result_26, %index_27 = control_merge [%falseResult_9, %falseResult_25]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %memEnd_1, %memEnd, %arg6 : <>, <>, <>
  }
}

