module {
  handshake.func @nested_loop(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: memref<1000xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "c", "a_start", "b_start", "c_start", "start"], resNames = ["a_end", "b_end", "c_end", "end"]} {
    %memEnd = mem_controller[%arg2 : memref<1000xi32>] %arg5 (%20, %addressResult_7, %dataResult_8) %result_21 {connectedBlocks = [2 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg1 : memref<1000xi32>] %arg4 (%addressResult_5) %result_21 {connectedBlocks = [2 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_1, %memEnd_2 = mem_controller[%arg0 : memref<1000xi32>] %arg3 (%addressResult) %result_21 {connectedBlocks = [2 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %0 = constant %arg6 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %2 = br %arg6 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %3 = mux %index [%1, %trueResult_17] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%2, %trueResult_19]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %4 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 0 : i32} : <>, <i32>
    %5 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %6 = constant %5 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 8 : i32} : <>, <i32>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant10", value = 7 : i32} : <>, <i32>
    %9 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %10 = constant %9 {handshake.bb = 1 : ui32, handshake.name = "constant11", value = 4 : i32} : <>, <i32>
    %11 = shli %3, %10 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %12 = shli %3, %8 {handshake.bb = 1 : ui32, handshake.name = "shli1"} : <i32>
    %13 = shli %3, %6 {handshake.bb = 1 : ui32, handshake.name = "shli2"} : <i32>
    %14 = addi %12, %13 {handshake.bb = 1 : ui32, handshake.name = "addi3"} : <i32>
    %15 = addi %11, %14 {handshake.bb = 1 : ui32, handshake.name = "addi4"} : <i32>
    %16 = br %4 {handshake.bb = 1 : ui32, handshake.name = "br4"} : <i32>
    %17 = br %3 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i32>
    %18 = br %15 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i32>
    %19 = br %result {handshake.bb = 1 : ui32, handshake.name = "br7"} : <>
    %20 = constant %result_3 {handshake.bb = 2 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %21 = mux %index_4 [%16, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %22 = mux %index_4 [%17, %trueResult_9] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %23 = mux %index_4 [%18, %trueResult_11] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_3, %index_4 = control_merge [%19, %trueResult_13]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %24 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %25 = constant %24 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 1 : i32} : <>, <i32>
    %26 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %27 = constant %26 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 1000 : i32} : <>, <i32>
    %28 = extui %21 {handshake.bb = 2 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %29 = trunci %28 {handshake.bb = 2 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%29] %outputs_1 {handshake.bb = 2 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %30 = extui %21 {handshake.bb = 2 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %31 = trunci %30 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_5, %dataResult_6 = load[%31] %outputs {handshake.bb = 2 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %32 = muli %dataResult, %dataResult_6 {handshake.bb = 2 : ui32, handshake.name = "muli1"} : <i32>
    %33 = addi %21, %23 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %34 = extui %33 {handshake.bb = 2 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %35 = trunci %34 {handshake.bb = 2 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_7, %dataResult_8 = store[%35] %32 {handshake.bb = 2 : ui32, handshake.name = "store2"} : <i32>, <i32>, <i32>, <i32>
    %36 = cmpi slt, %32, %27 {dynamatic.speculate = {max_predictions = 8 : i64, style = "standard"}, dynamatic.speculate.result_idx = 0 : i32, handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %37 = addi %21, %25 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %trueResult, %falseResult = cond_br %36, %37 {handshake.bb = 2 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_9, %falseResult_10 = cond_br %36, %22 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_11, %falseResult_12 = cond_br %36, %23 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_13, %falseResult_14 = cond_br %36, %result_3 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %38 = merge %falseResult_10 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %result_15, %index_16 = control_merge [%falseResult_14]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %39 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %40 = constant %39 {handshake.bb = 3 : ui32, handshake.name = "constant14", value = 2 : i32} : <>, <i32>
    %41 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %42 = constant %41 {handshake.bb = 3 : ui32, handshake.name = "constant15", value = 1 : i32} : <>, <i32>
    %43 = addi %38, %42 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i32>
    %44 = cmpi ne, %43, %40 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_17, %falseResult_18 = cond_br %44, %43 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_19, %falseResult_20 = cond_br %44, %result_15 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %result_21, %index_22 = control_merge [%falseResult_20]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %memEnd_2, %memEnd_0, %memEnd, %arg6 : <>, <>, <>, <>
  }
}

