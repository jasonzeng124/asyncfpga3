module {
  handshake.func @while_loop_3(%arg0: memref<100xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "bound", "a_start", "start"], resNames = ["a_end", "end"]} {
    %memEnd = mem_controller[%arg0 : memref<100xi32>] %arg2 (%11, %addressResult, %dataResult) %result_6 {connectedBlocks = [2 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> ()
    %0 = constant %arg3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i32>
    %2 = br %arg1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %3 = br %arg3 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %4 = mux %index [%1, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %5 = mux %index [%2, %trueResult_0] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%3, %trueResult_2]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %6 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %7 = constant %6 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %8 = muli %4, %4 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %9 = cmpi slt, %8, %5 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %10 = addi %4, %7 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %trueResult, %falseResult = cond_br %9, %10 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %9, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %9, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %trueResult_4, %falseResult_5 = cond_br %9, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %11 = constant %result_6 {handshake.bb = 2 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %12 = merge %falseResult_5 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %result_6, %index_7 = control_merge [%falseResult_3]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %13 = constant %result_6 {handshake.bb = 2 : ui32, handshake.name = "constant4", value = 0 : i32} : <>, <i32>
    %addressResult, %dataResult = store[%13] %12 {handshake.bb = 2 : ui32, handshake.name = "store0"} : <i32>, <i32>, <i32>, <i32>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %memEnd, %arg3 : <>, <>
  }
}

