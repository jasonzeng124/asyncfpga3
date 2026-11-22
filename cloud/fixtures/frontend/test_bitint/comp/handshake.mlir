module {
  handshake.func @test_bitint(%arg0: memref<10xi16>, %arg1: memref<10xi5>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["arr", "weight", "arr_start", "weight_start", "start"], resNames = ["out0", "arr_end", "weight_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg1 : memref<10xi5>] %arg3 (%addressResult_2) %result_8 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<i5>
    %outputs_0, %memEnd_1 = mem_controller[%arg0 : memref<10xi16>] %arg2 (%addressResult) %result_8 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<i16>
    %0 = constant %arg4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i32>
    %2 = br %arg4 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %3 = mux %index [%1, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %4 = mux %index [%1, %trueResult_4] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%2, %trueResult_6]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %6 = constant %5 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 10 : i32} : <>, <i32>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %9 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %10 = trunci %9 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%10] %outputs_0 {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i16>, <i32>, <i16>
    %11 = extui %dataResult {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i16> to <i21>
    %12 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %13 = trunci %12 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_2, %dataResult_3 = load[%13] %outputs {handshake.bb = 1 : ui32, handshake.name = "load1"} : <i32>, <i5>, <i32>, <i5>
    %14 = extui %dataResult_3 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i5> to <i21>
    %15 = muli %11, %14 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i21>
    %16 = extui %15 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i21> to <i32>
    %17 = addi %4, %16 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %18 = addi %3, %8 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %19 = cmpi ult, %18, %6 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %19, %18 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %19, %17 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %19, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %20 = merge %falseResult_5 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %result_8, %index_9 = control_merge [%falseResult_7]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %20, %memEnd_1, %memEnd, %arg4 : <i32>, <>, <>, <>
  }
}

