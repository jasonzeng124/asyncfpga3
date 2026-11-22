module {
  handshake.func @nested_loop(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: memref<1000xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "c", "a_start", "b_start", "c_start", "start"], resNames = ["a_end", "b_end", "c_end", "end"]} {
    %0:3 = fork [3] %arg6 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %memEnd = mem_controller[%arg2 : memref<1000xi32>] %arg5 (%36, %addressResult_7, %dataResult_8) %56#2 {connectedBlocks = [2 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg1 : memref<1000xi32>] %arg4 (%addressResult_5) %56#1 {connectedBlocks = [2 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %outputs_1, %memEnd_2 = mem_controller[%arg0 : memref<1000xi32>] %arg3 (%addressResult) %56#0 {connectedBlocks = [2 : i32], handshake.name = "mem_controller5"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %3 = extui %2 {handshake.bb = 0 : ui32, handshake.name = "extui3"} : <i1> to <i32>
    %4 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %5 = mux %index [%3, %trueResult_17] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %6:4 = fork [4] %5 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i32>
    %result, %index = control_merge [%4, %trueResult_19]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %7:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    %8 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %9 = constant %8 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 8 : i32} : <>, <i32>
    %10 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %11 = constant %10 {handshake.bb = 1 : ui32, handshake.name = "constant10", value = 7 : i32} : <>, <i32>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %13 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant11", value = 4 : i32} : <>, <i32>
    %14 = shli %6#3, %13 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %15 = shli %6#2, %11 {handshake.bb = 1 : ui32, handshake.name = "shli1"} : <i32>
    %16 = shli %6#1, %9 {handshake.bb = 1 : ui32, handshake.name = "shli2"} : <i32>
    %17 = addi %15, %16 {handshake.bb = 1 : ui32, handshake.name = "addi3"} : <i32>
    %18 = addi %14, %17 {handshake.bb = 1 : ui32, handshake.name = "addi4"} : <i32>
    %19 = constant %7#0 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %20 = br %19 {handshake.bb = 1 : ui32, handshake.name = "br4"} : <i1>
    %21 = extui %20 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i1> to <i32>
    %22 = br %6#0 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i32>
    %23 = br %18 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i32>
    %24 = br %7#1 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <>
    %25 = mux %34#0 [%21, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %26:4 = fork [4] %25 {handshake.bb = 2 : ui32, handshake.name = "fork3"} : <i32>
    %27 = trunci %26#0 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i32> to <i10>
    %28 = trunci %26#1 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i32> to <i10>
    %29 = trunci %26#2 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i32> to <i10>
    %30 = mux %34#1 [%22, %trueResult_9] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %31 = mux %34#2 [%23, %trueResult_11] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %32:2 = fork [2] %31 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i32>
    %33 = trunci %32#0 {handshake.bb = 2 : ui32, handshake.name = "trunci3"} : <i32> to <i10>
    %result_3, %index_4 = control_merge [%24, %trueResult_13]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %34:3 = fork [3] %index_4 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i1>
    %35:2 = fork [2] %result_3 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <>
    %36 = constant %35#0 {handshake.bb = 2 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %37 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %38 = constant %37 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 1 : i32} : <>, <i32>
    %39 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %40 = constant %39 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 1000 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%29] %outputs_1 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %addressResult_5, %dataResult_6 = load[%28] %outputs {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i10>, <i32>, <i10>, <i32>
    %41 = muli %dataResult, %dataResult_6 {handshake.bb = 2 : ui32, handshake.name = "muli1"} : <i32>
    %42:2 = fork [2] %41 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i32>
    %43 = addi %27, %33 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i10>
    %addressResult_7, %dataResult_8 = store[%43] %42#0 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store2"} : <i10>, <i32>, <i10>, <i32>
    %44 = cmpi slt, %42#1, %40 {dynamatic.speculate = {max_predictions = 8 : i64, style = "standard"}, dynamatic.speculate.result_idx = 0 : i32, handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %45:4 = fork [4] %44 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i1>
    %46 = addi %26#3, %38 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %trueResult, %falseResult = cond_br %45#3, %46 {handshake.bb = 2 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    sink %falseResult {handshake.name = "sink0"} : <i32>
    %trueResult_9, %falseResult_10 = cond_br %45#2, %30 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_11, %falseResult_12 = cond_br %45#1, %32#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    sink %falseResult_12 {handshake.name = "sink1"} : <i32>
    %trueResult_13, %falseResult_14 = cond_br %45#0, %35#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %47 = merge %falseResult_10 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %result_15, %index_16 = control_merge [%falseResult_14]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_16 {handshake.name = "sink2"} : <i1>
    %48 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %49 = constant %48 {handshake.bb = 3 : ui32, handshake.name = "constant14", value = 2 : i32} : <>, <i32>
    %50 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %51 = constant %50 {handshake.bb = 3 : ui32, handshake.name = "constant15", value = 1 : i32} : <>, <i32>
    %52 = addi %47, %51 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i32>
    %53:2 = fork [2] %52 {handshake.bb = 3 : ui32, handshake.name = "fork9"} : <i32>
    %54 = cmpi ne, %53#1, %49 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %55:2 = fork [2] %54 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i1>
    %trueResult_17, %falseResult_18 = cond_br %55#1, %53#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    sink %falseResult_18 {handshake.name = "sink3"} : <i32>
    %trueResult_19, %falseResult_20 = cond_br %55#0, %result_15 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %result_21, %index_22 = control_merge [%falseResult_20]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_22 {handshake.name = "sink4"} : <i1>
    %56:3 = fork [3] %result_21 {handshake.bb = 4 : ui32, handshake.name = "fork11"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %memEnd_2, %memEnd_0, %memEnd, %0#1 : <>, <>, <>, <>
  }
}

