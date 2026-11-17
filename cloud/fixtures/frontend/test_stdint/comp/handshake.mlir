module {
  handshake.func @test_stdint(%arg0: memref<100xi8>, %arg1: !handshake.channel<i8>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "a_start", "start"], resNames = ["a_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg0 : memref<100xi8>] %arg2 (%4, %addressResult, %addressResult_0, %dataResult_1) %result_6 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i8>) -> !handshake.channel<i8>
    %0 = constant %arg3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i32>
    %2 = br %arg1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i8>
    %3 = br %arg3 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %4 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %5 = mux %index [%1, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %6 = mux %index [%2, %trueResult_2] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i8>, <i8>] to <i8>
    %result, %index = control_merge [%3, %trueResult_4]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 100 : i32} : <>, <i32>
    %9 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %10 = constant %9 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %11 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %12 = trunci %11 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%12] %outputs {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i8>, <i32>, <i8>
    %13 = muli %dataResult, %dataResult {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i8>
    %14 = muli %13, %dataResult {handshake.bb = 1 : ui32, handshake.name = "muli1"} : <i8>
    %15 = addi %14, %6 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i8>
    %16 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %17 = trunci %16 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_0, %dataResult_1 = store[%17] %15 {handshake.bb = 1 : ui32, handshake.name = "store1"} : <i32>, <i8>, <i32>, <i8>
    %18 = addi %5, %10 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %19 = cmpi ult, %18, %8 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %19, %18 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %19, %6 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i8>
    %trueResult_4, %falseResult_5 = cond_br %19, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %result_6, %index_7 = control_merge [%falseResult_5]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %memEnd, %arg3 : <>, <>
  }
}

