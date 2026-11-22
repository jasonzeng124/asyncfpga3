module {
  handshake.func @while_loop_2(%arg0: memref<1000xi32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:2 = lsq[%arg0 : memref<1000xi32>] (%arg1, %result, %addressResult, %result_4, %addressResult_6, %dataResult_7, %result_4)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %1 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i32>
    %3 = br %arg2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %4 = mux %index [%2, %falseResult_3] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%3, %falseResult_1]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %6 = constant %5 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 0 : i32} : <>, <i32>
    %9 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %10 = trunci %9 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%10] %0#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %11 = cmpi eq, %dataResult, %8 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %12 = addi %4, %6 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %trueResult, %falseResult = cond_br %11, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %11, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %11, %12 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %13 = merge %trueResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %result_4, %index_5 = control_merge [%trueResult_0]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %14 = constant %result_4 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 0 : i32} : <>, <i32>
    %addressResult_6, %dataResult_7 = store[%14] %13 {handshake.bb = 2 : ui32, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %0#1, %arg2 : <>, <>
  }
}

