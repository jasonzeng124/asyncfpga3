module {
  handshake.func @fill(%arg0: memref<32xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "n", "x", "a_start", "start"], resNames = ["out0", "a_end", "end"]} {
    %memEnd = mem_controller[%arg0 : memref<32xi32>] %arg3 (%3, %addressResult, %dataResult) %result_20 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> ()
    %0 = constant %arg4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = constant %arg4 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 3 : i32} : <>, <i32>
    %2 = cmpi sgt, %arg1, %0 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %2, %0 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %2, %1 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %2, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %2, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %2, %arg4 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %3 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %4 = mux %index [%trueResult, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %5 = mux %index [%trueResult_0, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %6 = mux %index [%trueResult_2, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %7 = mux %index [%trueResult, %trueResult_14] {handshake.bb = 1 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %8 = mux %index [%trueResult_4, %trueResult_16] {handshake.bb = 1 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_6, %trueResult_18]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %9 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %10 = constant %9 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %11 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %12 = constant %11 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 31 : i32} : <>, <i32>
    %13 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %14 = constant %13 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 7 : i32} : <>, <i32>
    %15 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %16 = constant %15 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 5 : i32} : <>, <i32>
    %17 = source {handshake.bb = 1 : ui32, handshake.name = "source4"} : <>
    %18 = constant %17 {handshake.bb = 1 : ui32, handshake.name = "constant10", value = 3 : i32} : <>, <i32>
    %19 = shli %6, %16 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %20 = xori %6, %19 {handshake.bb = 1 : ui32, handshake.name = "xori0"} : <i32>
    %21 = addi %20, %4 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %22 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %23 = trunci %22 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = store[%23] %21 {handshake.bb = 1 : ui32, handshake.name = "store0"} : <i32>, <i32>, <i32>, <i32>
    %24 = addi %5, %14 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %25 = andi %24, %12 {handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i32>
    %26 = shrsi %21, %18 {handshake.bb = 1 : ui32, handshake.name = "shrsi0"} : <i32>
    %27 = addi %7, %26 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %28 = addi %4, %10 {handshake.bb = 1 : ui32, handshake.name = "addi3"} : <i32>
    %29 = cmpi slt, %28, %8 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_8, %falseResult_9 = cond_br %29, %28 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %29, %25 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %29, %21 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %29, %27 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %29, %8 {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %29, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br12"} : <i1>, <>
    %30 = mux %index_21 [%falseResult, %falseResult_15] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %result_20, %index_21 = control_merge [%falseResult_7, %falseResult_19]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %30, %memEnd, %arg4 : <i32>, <>, <>
  }
}

