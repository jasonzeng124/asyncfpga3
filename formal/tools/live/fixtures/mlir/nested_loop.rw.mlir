module {
  handshake.func @nested_loop(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: memref<1000xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "c", "a_start", "b_start", "c_start", "start"], resNames = ["a_end", "b_end", "c_end", "end"]} {
    %0:3 = fork [3] %arg6 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %memEnd = mem_controller[%arg2 : memref<1000xi32>] %arg5 (%37, %addressResult_7, %dataResult_8) %59#2 {connectedBlocks = [2 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg1 : memref<1000xi32>] %arg4 (%addressResult_5) %59#1 {connectedBlocks = [2 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %outputs_1, %memEnd_2 = mem_controller[%arg0 : memref<1000xi32>] %arg3 (%addressResult) %59#0 {connectedBlocks = [2 : i32], handshake.name = "mem_controller5"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %3 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %4 = mux %index [%2, %trueResult_17] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i1>, <i1>] to <i1>
    %5:2 = fork [2] %4 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i1>
    %6 = extui %5#1 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i1> to <i32>
    %7:3 = fork [3] %6 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i32>
    %result, %index = control_merge [%3, %trueResult_19]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %8:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <>
    %9 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %10 = constant %9 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 8 : i32} : <>, <i32>
    %11 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %12 = constant %11 {handshake.bb = 1 : ui32, handshake.name = "constant10", value = 7 : i32} : <>, <i32>
    %13 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %14 = constant %13 {handshake.bb = 1 : ui32, handshake.name = "constant11", value = 4 : i32} : <>, <i32>
    %15 = shli %7#0, %14 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %16 = shli %7#1, %12 {handshake.bb = 1 : ui32, handshake.name = "shli1"} : <i32>
    %17 = shli %7#2, %10 {handshake.bb = 1 : ui32, handshake.name = "shli2"} : <i32>
    %18 = addi %16, %17 {handshake.bb = 1 : ui32, handshake.name = "addi3"} : <i32>
    %19 = addi %15, %18 {handshake.bb = 1 : ui32, handshake.name = "addi4"} : <i32>
    %20 = constant %8#0 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %21 = br %20 {handshake.bb = 1 : ui32, handshake.name = "br4"} : <i1>
    %22 = extui %21 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i1> to <i32>
    %23 = br %5#0 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i1>
    %24 = br %19 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i32>
    %25 = br %8#1 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <>
    %26 = mux %35#1 [%22, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %27:4 = fork [4] %26 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i32>
    %28 = trunci %27#0 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i32> to <i10>
    %29 = trunci %27#1 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i32> to <i10>
    %30 = trunci %27#2 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i32> to <i10>
    %31 = mux %35#0 [%23, %trueResult_9] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i1>, <i1>] to <i1>
    %32 = mux %35#2 [%24, %trueResult_11] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %33:2 = fork [2] %32 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i32>
    %34 = trunci %33#0 {handshake.bb = 2 : ui32, handshake.name = "trunci3"} : <i32> to <i10>
    %result_3, %index_4 = control_merge [%25, %trueResult_13]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %35:3 = fork [3] %index_4 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i1>
    %36:2 = fork [2] %result_3 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <>
    %37 = constant %36#0 {handshake.bb = 2 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %38 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %39 = constant %38 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 1 : i32} : <>, <i32>
    %40 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %41 = constant %40 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 1000 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%30] %outputs_1 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %addressResult_5, %dataResult_6 = load[%29] %outputs {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i10>, <i32>, <i10>, <i32>
    %42 = muli %dataResult, %dataResult_6 {handshake.bb = 2 : ui32, handshake.name = "muli1"} : <i32>
    %43:2 = fork [2] %42 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i32>
    %44 = addi %28, %34 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i10>
    %addressResult_7, %dataResult_8 = store[%44] %43#0 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store2"} : <i10>, <i32>, <i10>, <i32>
    %45 = cmpi slt, %43#1, %41 {dynamatic.speculate = {max_predictions = 8 : i64, style = "standard"}, dynamatic.speculate.result_idx = 0 : i32, handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %46:4 = fork [4] %45 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i1>
    %47 = addi %27#3, %39 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %trueResult, %falseResult = cond_br %46#3, %47 {handshake.bb = 2 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    sink %falseResult {handshake.name = "sink0"} : <i32>
    %trueResult_9, %falseResult_10 = cond_br %46#0, %31 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <i1>
    %trueResult_11, %falseResult_12 = cond_br %46#2, %33#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    sink %falseResult_12 {handshake.name = "sink1"} : <i32>
    %trueResult_13, %falseResult_14 = cond_br %46#1, %36#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %48 = merge %falseResult_10 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i1>
    %49 = extui %48 {handshake.bb = 3 : ui32, handshake.name = "extui5"} : <i1> to <i2>
    %50 = constant %52 {handshake.bb = 3 : ui32, handshake.name = "constant5", value = 1 : i2} : <>, <i2>
    %result_15, %index_16 = control_merge [%falseResult_14]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_16 {handshake.name = "sink2"} : <i1>
    %51 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %52 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %53 = addi %49, %50 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i2>
    %54:2 = fork [2] %53 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i2>
    %55 = trunci %54#0 {handshake.bb = 3 : ui32, handshake.name = "trunci4"} : <i2> to <i1>
    %56 = constant %51 {handshake.bb = 3 : ui32, handshake.name = "constant6", value = -2 : i2} : <>, <i2>
    %57 = cmpi ult, %54#1, %56 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i2>
    %58:2 = fork [2] %57 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i1>
    %trueResult_17, %falseResult_18 = cond_br %58#0, %55 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <i1>
    sink %falseResult_18 {handshake.name = "sink3"} : <i1>
    %trueResult_19, %falseResult_20 = cond_br %58#1, %result_15 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %result_21, %index_22 = control_merge [%falseResult_20]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_22 {handshake.name = "sink4"} : <i1>
    %59:3 = fork [3] %result_21 {handshake.bb = 4 : ui32, handshake.name = "fork12"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %memEnd_2, %memEnd_0, %memEnd, %0#1 : <>, <>, <>, <>
  }
}

