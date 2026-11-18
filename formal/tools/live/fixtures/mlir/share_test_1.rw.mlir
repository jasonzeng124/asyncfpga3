module {
  handshake.func @share_test_1(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "a_start", "b_start", "start"], resNames = ["out0", "a_end", "b_end", "end"]} {
    %0:3 = fork [3] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs:2, %memEnd = mem_controller[%arg1 : memref<1000xi32>] %arg3 (%addressResult_2, %addressResult_14) %54#1 {connectedBlocks = [1 : i32, 2 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i10>, !handshake.channel<i10>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %outputs_0:2, %memEnd_1 = mem_controller[%arg0 : memref<1000xi32>] %arg2 (%addressResult, %addressResult_12) %54#0 {connectedBlocks = [1 : i32, 2 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i10>, !handshake.channel<i10>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %3:2 = fork [2] %2 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i1>
    %4 = extui %3#1 {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i1> to <i32>
    %5 = extui %3#0 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i1> to <i10>
    %6 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %7 = mux %12#1 [%4, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %8 = mux %12#0 [%5, %trueResult_4] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i10>, <i10>] to <i10>
    %9:3 = fork [3] %8 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i10>
    %10 = extui %9#2 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i10> to <i11>
    %11 = constant %15 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i11} : <>, <i11>
    %result, %index = control_merge [%6, %trueResult_6]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %12:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i1>
    %13:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <>
    %14 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %15 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %16 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %17 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %18 = constant %17 {handshake.bb = 1 : ui32, handshake.name = "constant10", value = 2 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%9#1] %outputs_0#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %19 = constant %16 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = -25 : i10} : <>, <i10>
    %20 = subi %19, %9#0 {handshake.bb = 1 : ui32, handshake.name = "subi0"} : <i10>
    %addressResult_2, %dataResult_3 = load[%20] %outputs#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i10>, <i32>, <i10>, <i32>
    %21 = muli %dataResult, %dataResult_3 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %22:2 = fork [2] %21 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %23 = shli %22#1, %18 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %24 = addi %22#0, %23 {handshake.bb = 1 : ui32, handshake.name = "addi4"} : <i32>
    %25 = addi %7, %24 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %26 = addi %10, %11 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i11>
    %27:2 = fork [2] %26 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i11>
    %28 = trunci %27#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i11> to <i10>
    %29 = constant %14 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1000 : i11} : <>, <i11>
    %30 = cmpi ult, %27#1, %29 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i11>
    %31:4 = fork [4] %30 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i1>
    %trueResult, %falseResult = cond_br %31#1, %25 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %31#0, %28 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i10>
    sink %falseResult_5 {handshake.name = "sink0"} : <i10>
    %trueResult_6, %falseResult_7 = cond_br %31#2, %13#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %32 = constant %13#0 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = false} : <>, <i1>
    %trueResult_8, %falseResult_9 = cond_br %31#3, %32 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i1>
    sink %trueResult_8 {handshake.name = "sink1"} : <i1>
    %33 = extui %falseResult_9 {handshake.bb = 2 : ui32, handshake.name = "extui5"} : <i1> to <i10>
    %34 = mux %39#1 [%falseResult, %trueResult_16] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %35 = mux %39#0 [%33, %trueResult_18] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i10>, <i10>] to <i10>
    %36:3 = fork [3] %35 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i10>
    %37 = extui %36#2 {handshake.bb = 2 : ui32, handshake.name = "extui6"} : <i10> to <i11>
    %38 = constant %41 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = 1 : i11} : <>, <i11>
    %result_10, %index_11 = control_merge [%falseResult_7, %trueResult_20]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %39:2 = fork [2] %index_11 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i1>
    %40 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %41 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %42 = source {handshake.bb = 2 : ui32, handshake.name = "source6"} : <>
    %43 = constant %42 {handshake.bb = 2 : ui32, handshake.name = "constant15", value = -25 : i10} : <>, <i10>
    %44 = subi %43, %36#0 {handshake.bb = 2 : ui32, handshake.name = "subi1"} : <i10>
    %addressResult_12, %dataResult_13 = load[%44] %outputs_0#1 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load2"} : <i10>, <i32>, <i10>, <i32>
    %addressResult_14, %dataResult_15 = load[%36#1] %outputs#1 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load3"} : <i10>, <i32>, <i10>, <i32>
    %45 = muli %dataResult_13, %dataResult_15 {handshake.bb = 2 : ui32, handshake.name = "muli2"} : <i32>
    %46 = addi %34, %45 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %47 = addi %37, %38 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i11>
    %48:2 = fork [2] %47 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <i11>
    %49 = trunci %48#0 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i11> to <i10>
    %50 = constant %40 {handshake.bb = 2 : ui32, handshake.name = "constant16", value = 1000 : i11} : <>, <i11>
    %51 = cmpi ult, %48#1, %50 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i11>
    %52:3 = fork [3] %51 {handshake.bb = 2 : ui32, handshake.name = "fork11"} : <i1>
    %trueResult_16, %falseResult_17 = cond_br %52#1, %46 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %52#0, %49 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i10>
    sink %falseResult_19 {handshake.name = "sink2"} : <i10>
    %trueResult_20, %falseResult_21 = cond_br %52#2, %result_10 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %53 = merge %falseResult_17 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %result_22, %index_23 = control_merge [%falseResult_21]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_23 {handshake.name = "sink3"} : <i1>
    %54:2 = fork [2] %result_22 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %53, %memEnd_1, %memEnd, %0#1 : <i32>, <>, <>, <>
  }
}

