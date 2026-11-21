module {
  handshake.func @share_test_1(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "a_start", "b_start", "start"], resNames = ["out0", "a_end", "b_end", "end"]} {
    %outputs:2, %memEnd = mem_controller[%arg1 : memref<1000xi32>] %arg3 (%addressResult_2, %addressResult_14) %result_22 {connectedBlocks = [1 : i32, 2 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %outputs_0:2, %memEnd_1 = mem_controller[%arg0 : memref<1000xi32>] %arg2 (%addressResult, %addressResult_12) %result_22 {connectedBlocks = [1 : i32, 2 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %0 = constant %arg4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i32>
    %2 = br %arg4 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %3 = mux %index [%1, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %4 = mux %index [%1, %trueResult_4] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%2, %trueResult_6]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %6 = constant %5 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 1000 : i32} : <>, <i32>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %9 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %10 = constant %9 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 999 : i32} : <>, <i32>
    %11 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 0 : i32} : <>, <i32>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %13 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant10", value = 2 : i32} : <>, <i32>
    %14 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %15 = trunci %14 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%15] %outputs_0#0 {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %16 = subi %10, %4 {handshake.bb = 1 : ui32, handshake.name = "subi0"} : <i32>
    %17 = trunci %16 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i32> to <i32>
    %addressResult_2, %dataResult_3 = load[%17] %outputs#0 {handshake.bb = 1 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %18 = muli %dataResult, %dataResult_3 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %19 = shli %18, %13 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %20 = addi %18, %19 {handshake.bb = 1 : ui32, handshake.name = "addi4"} : <i32>
    %21 = addi %3, %20 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %22 = addi %4, %8 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %23 = cmpi ult, %22, %6 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %23, %21 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %23, %22 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %23, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %trueResult_8, %falseResult_9 = cond_br %23, %11 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %24 = mux %index_11 [%falseResult, %trueResult_16] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %25 = mux %index_11 [%falseResult_9, %trueResult_18] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_10, %index_11 = control_merge [%falseResult_7, %trueResult_20]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %26 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %27 = constant %26 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 1000 : i32} : <>, <i32>
    %28 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %29 = constant %28 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 1 : i32} : <>, <i32>
    %30 = source {handshake.bb = 2 : ui32, handshake.name = "source6"} : <>
    %31 = constant %30 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 999 : i32} : <>, <i32>
    %32 = subi %31, %25 {handshake.bb = 2 : ui32, handshake.name = "subi1"} : <i32>
    %33 = trunci %32 {handshake.bb = 2 : ui32, handshake.name = "index_cast2"} : <i32> to <i32>
    %addressResult_12, %dataResult_13 = load[%33] %outputs_0#1 {handshake.bb = 2 : ui32, handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    %34 = extui %25 {handshake.bb = 2 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %35 = trunci %34 {handshake.bb = 2 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_14, %dataResult_15 = load[%35] %outputs#1 {handshake.bb = 2 : ui32, handshake.name = "load3"} : <i32>, <i32>, <i32>, <i32>
    %36 = muli %dataResult_13, %dataResult_15 {handshake.bb = 2 : ui32, handshake.name = "muli2"} : <i32>
    %37 = addi %24, %36 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %38 = addi %25, %29 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i32>
    %39 = cmpi ult, %38, %27 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_16, %falseResult_17 = cond_br %39, %37 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %39, %38 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %39, %result_10 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %40 = merge %falseResult_17 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %result_22, %index_23 = control_merge [%falseResult_21]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %40, %memEnd_1, %memEnd, %arg4 : <i32>, <>, <>, <>
  }
}

