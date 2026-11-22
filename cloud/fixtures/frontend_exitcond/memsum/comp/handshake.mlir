module {
  handshake.func @memsum(%arg0: memref<32xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "n", "a_start", "start"], resNames = ["out0", "a_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg0 : memref<32xi32>] %arg2 (%addressResult) %result_14 {connectedBlocks = [2 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %0 = constant %arg3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = cmpi sgt, %arg1, %0 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %1, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %1, %arg3 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %1, %0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %2 = merge %trueResult {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %result, %index = control_merge [%trueResult_0]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    %3 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %4 = constant %3 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %5 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %6 = constant %5 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 31 : i32} : <>, <i32>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = -1 : i32} : <>, <i32>
    %9 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 0 : i32} : <>, <i32>
    %10 = addi %2, %8 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %11 = minui %10, %6 {handshake.bb = 1 : ui32, handshake.name = "minui0"} : <i32>
    %12 = addi %11, %4 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %13 = br %9 {handshake.bb = 1 : ui32, handshake.name = "br1"} : <i32>
    %14 = br %12 {handshake.bb = 1 : ui32, handshake.name = "br2"} : <i32>
    %15 = br %result {handshake.bb = 1 : ui32, handshake.name = "br3"} : <>
    %16 = mux %index_5 [%13, %trueResult_6] {handshake.bb = 2 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %17 = mux %index_5 [%13, %trueResult_8] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %18 = mux %index_5 [%14, %trueResult_10] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result_4, %index_5 = control_merge [%15, %trueResult_12]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %19 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %20 = constant %19 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 1 : i32} : <>, <i32>
    %21 = extui %16 {handshake.bb = 2 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %22 = trunci %21 {handshake.bb = 2 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%22] %outputs {handshake.bb = 2 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %23 = addi %16, %20 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %24 = muli %dataResult, %23 {handshake.bb = 2 : ui32, handshake.name = "muli0"} : <i32>
    %25 = addi %17, %24 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i32>
    %26 = addi %16, %20 {handshake.bb = 2 : ui32, handshake.name = "addi4"} : <i32>
    %27 = cmpi ne, %26, %18 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %27, %26 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %27, %25 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %27, %18 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %27, %result_4 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %28 = mux %index_15 [%falseResult_3, %falseResult_9] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_14, %index_15 = control_merge [%falseResult_1, %falseResult_13]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %28, %memEnd, %arg3 : <i32>, <>, <>
  }
}

