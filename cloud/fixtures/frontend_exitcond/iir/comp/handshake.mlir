module {
  handshake.func @iir(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.channel<i32>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["y", "x", "a", "b", "y_start", "x_start", "start"], resNames = ["out0", "y_end", "x_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg1 : memref<1000xi32>] %arg5 (%addressResult_2) %result_14 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_0, %memEnd_1 = mem_controller[%arg0 : memref<1000xi32>] %arg4 (%addressResult, %7, %addressResult_4, %dataResult_5) %result_14 {connectedBlocks = [0 : i32, 1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %0 = constant %arg6 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %1 = constant %arg6 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = 0 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%1] %outputs_0 {handshake.bb = 0 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %2 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i32>
    %3 = br %dataResult {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %4 = br %arg2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %5 = br %arg3 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <i32>
    %6 = br %arg6 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <>
    %7 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %8 = mux %index [%2, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %9 = mux %index [%3, %trueResult_6] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %10 = mux %index [%4, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %11 = mux %index [%5, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%6, %trueResult_12]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %13 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1000 : i32} : <>, <i32>
    %14 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %15 = constant %14 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %16 = muli %9, %10 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %17 = extui %8 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %18 = trunci %17 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult_2, %dataResult_3 = load[%18] %outputs {handshake.bb = 1 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %19 = muli %dataResult_3, %11 {handshake.bb = 1 : ui32, handshake.name = "muli1"} : <i32>
    %20 = addi %16, %19 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %21 = extui %8 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %22 = trunci %21 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_4, %dataResult_5 = store[%22] %20 {handshake.bb = 1 : ui32, handshake.name = "store2"} : <i32>, <i32>, <i32>, <i32>
    %23 = addi %8, %15 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %24 = cmpi ne, %23, %13 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %24, %23 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %24, %20 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %24, %10 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %24, %11 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %24, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %25 = merge %falseResult_7 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %result_14, %index_15 = control_merge [%falseResult_13]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %25, %memEnd_1, %memEnd, %arg6 : <i32>, <>, <>, <>
  }
}

