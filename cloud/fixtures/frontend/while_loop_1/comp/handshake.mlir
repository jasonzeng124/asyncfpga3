module {
  handshake.func @while_loop_1(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "a_start", "b_start", "start"], resNames = ["a_end", "b_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg1 : memref<1000xi32>] %arg3 (%addressResult_0) %result_6 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %0:2 = lsq[%arg0 : memref<1000xi32>] (%arg2, %result, %addressResult, %addressResult_2, %dataResult_3, %result_6)  {groupSizes = [2 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %1 = constant %arg4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i32>
    %3 = br %arg4 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %4 = mux %index [%2, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%3, %trueResult_4]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %6 = constant %5 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1000 : i32} : <>, <i32>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %9 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %10 = trunci %9 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%10] %0#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %11 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %12 = trunci %11 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_0, %dataResult_1 = load[%12] %outputs {handshake.bb = 1 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %13 = addi %dataResult, %dataResult_1 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %14 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %15 = trunci %14 {handshake.bb = 1 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_2, %dataResult_3 = store[%15] %13 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : <i32>, <i32>, <i32>, <i32>
    %16 = addi %4, %8 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %17 = cmpi slt, %13, %6 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %17, %16 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %17, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <>
    %result_6, %index_7 = control_merge [%falseResult_5]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %0#1, %memEnd, %arg4 : <>, <>, <>
  }
}

