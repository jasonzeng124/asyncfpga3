module {
  handshake.func @binary_search(%arg0: !handshake.channel<i32>, %arg1: memref<101xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["search", "a", "a_start", "start"], resNames = ["out0", "a_end", "end"]} {
    %outputs:2, %memEnd = mem_controller[%arg1 : memref<101xi32>] %arg2 (%addressResult, %addressResult_18) %result_40 {connectedBlocks = [1 : i32, 4 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %0 = constant %arg3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %2 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %3 = br %arg3 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %4 = mux %index [%1, %trueResult_6] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %5 = mux %index [%2, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%3, %trueResult_10]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %6 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %7 = trunci %6 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%7] %outputs#0 {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %8 = cmpi eq, %dataResult, %5 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %8, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %8, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %8, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %9 = merge %falseResult_1 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %10 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %result_4, %index_5 = control_merge [%falseResult_3]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %11 = constant %result_4 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = -1 : i32} : <>, <i32>
    %12 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %13 = constant %12 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 101 : i32} : <>, <i32>
    %14 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %15 = constant %14 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = 2 : i32} : <>, <i32>
    %16 = addi %10, %15 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %17 = cmpi ult, %16, %13 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %17, %16 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %17, %9 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %17, %result_4 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %trueResult_12, %falseResult_13 = cond_br %17, %11 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %18 = mux %index_15 [%trueResult, %falseResult_13] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %19 = mux %index_15 [%trueResult_0, %falseResult_9] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_14, %index_15 = control_merge [%trueResult_2, %falseResult_11]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %20 = constant %result_14 {handshake.bb = 3 : ui32, handshake.name = "constant8", value = 1 : i32} : <>, <i32>
    %21 = br %20 {handshake.bb = 3 : ui32, handshake.name = "br5"} : <i32>
    %22 = br %19 {handshake.bb = 3 : ui32, handshake.name = "br6"} : <i32>
    %23 = br %18 {handshake.bb = 3 : ui32, handshake.name = "br7"} : <i32>
    %24 = br %result_14 {handshake.bb = 3 : ui32, handshake.name = "br8"} : <>
    %25 = mux %index_17 [%21, %trueResult_30] {handshake.bb = 4 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %26 = mux %index_17 [%22, %trueResult_32] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %27 = mux %index_17 [%23, %trueResult_34] {handshake.bb = 4 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %result_16, %index_17 = control_merge [%24, %trueResult_36]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %28 = extui %25 {handshake.bb = 4 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %29 = trunci %28 {handshake.bb = 4 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_18, %dataResult_19 = load[%29] %outputs#1 {handshake.bb = 4 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %30 = cmpi eq, %dataResult_19, %26 {handshake.bb = 4 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_20, %falseResult_21 = cond_br %30, %25 {handshake.bb = 4 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %30, %27 {handshake.bb = 4 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %30, %result_16 {handshake.bb = 4 : ui32, handshake.name = "cond_br13"} : <i1>, <>
    %trueResult_26, %falseResult_27 = cond_br %30, %26 {handshake.bb = 4 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %31 = merge %falseResult_27 {handshake.bb = 5 : ui32, handshake.name = "merge2"} : <i32>
    %32 = merge %falseResult_23 {handshake.bb = 5 : ui32, handshake.name = "merge3"} : <i32>
    %33 = merge %falseResult_21 {handshake.bb = 5 : ui32, handshake.name = "merge4"} : <i32>
    %result_28, %index_29 = control_merge [%falseResult_25]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    %34 = constant %result_28 {handshake.bb = 5 : ui32, handshake.name = "constant9", value = -1 : i32} : <>, <i32>
    %35 = source {handshake.bb = 5 : ui32, handshake.name = "source2"} : <>
    %36 = constant %35 {handshake.bb = 5 : ui32, handshake.name = "constant10", value = 101 : i32} : <>, <i32>
    %37 = source {handshake.bb = 5 : ui32, handshake.name = "source3"} : <>
    %38 = constant %37 {handshake.bb = 5 : ui32, handshake.name = "constant11", value = 2 : i32} : <>, <i32>
    %39 = addi %33, %38 {handshake.bb = 5 : ui32, handshake.name = "addi1"} : <i32>
    %40 = cmpi ult, %39, %36 {handshake.bb = 5 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_30, %falseResult_31 = cond_br %40, %39 {handshake.bb = 5 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %trueResult_32, %falseResult_33 = cond_br %40, %31 {handshake.bb = 5 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_34, %falseResult_35 = cond_br %40, %32 {handshake.bb = 5 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_36, %falseResult_37 = cond_br %40, %result_28 {handshake.bb = 5 : ui32, handshake.name = "cond_br18"} : <i1>, <>
    %trueResult_38, %falseResult_39 = cond_br %40, %34 {handshake.bb = 5 : ui32, handshake.name = "cond_br19"} : <i1>, <i32>
    %41 = mux %index_41 [%trueResult_20, %falseResult_39] {handshake.bb = 6 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %42 = mux %index_41 [%trueResult_22, %falseResult_35] {handshake.bb = 6 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %result_40, %index_41 = control_merge [%trueResult_24, %falseResult_37]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>, <>] to <>, <i1>
    %43 = source {handshake.bb = 6 : ui32, handshake.name = "source4"} : <>
    %44 = constant %43 {handshake.bb = 6 : ui32, handshake.name = "constant12", value = -1 : i32} : <>, <i32>
    %45 = cmpi eq, %42, %44 {handshake.bb = 6 : ui32, handshake.name = "cmpi4"} : <i32>
    %46 = select %45[%41, %42] {handshake.bb = 6 : ui32, handshake.name = "select1"} : <i1>, <i32>
    end {handshake.bb = 6 : ui32, handshake.name = "end0"} %46, %memEnd, %arg3 : <i32>, <>, <>
  }
}

