module {
  handshake.func @share_test_1(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "a_start", "b_start", "start"], resNames = ["out0", "a_end", "b_end", "end"]} {
    %0:3 = fork [3] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs:2, %memEnd = mem_controller[%arg1 : memref<1000xi32>] %arg3 (%addressResult_2, %addressResult_14) %53#1 {connectedBlocks = [1 : i32, 2 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i10>, !handshake.channel<i10>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %outputs_0:2, %memEnd_1 = mem_controller[%arg0 : memref<1000xi32>] %arg2 (%addressResult, %addressResult_12) %53#0 {connectedBlocks = [1 : i32, 2 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i10>, !handshake.channel<i10>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %3 = extui %2 {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i1> to <i32>
    %4:2 = fork [2] %3 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %5 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %6 = mux %11#0 [%4#0, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %7 = mux %11#1 [%4#1, %trueResult_4] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %8:3 = fork [3] %7 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i32>
    %9 = trunci %8#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i10>
    %10 = trunci %8#1 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i10>
    %result, %index = control_merge [%5, %trueResult_6]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %11:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i1>
    %12:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <>
    %13 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %14 = constant %13 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 1000 : i32} : <>, <i32>
    %15 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %16 = constant %15 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %17 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %18 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %19 = constant %18 {handshake.bb = 1 : ui32, handshake.name = "constant10", value = 2 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%10] %outputs_0#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %20 = constant %17 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = -25 : i10} : <>, <i10>
    %21 = subi %20, %9 {handshake.bb = 1 : ui32, handshake.name = "subi0"} : <i10>
    %addressResult_2, %dataResult_3 = load[%21] %outputs#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i10>, <i32>, <i10>, <i32>
    %22 = muli %dataResult, %dataResult_3 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %23:2 = fork [2] %22 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %24 = shli %23#1, %19 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %25 = addi %23#0, %24 {handshake.bb = 1 : ui32, handshake.name = "addi4"} : <i32>
    %26 = addi %6, %25 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %27 = addi %8#2, %16 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %28:2 = fork [2] %27 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i32>
    %29 = cmpi ne, %28#1, %14 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %30:4 = fork [4] %29 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i1>
    %trueResult, %falseResult = cond_br %30#3, %26 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %30#2, %28#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    sink %falseResult_5 {handshake.name = "sink0"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %30#1, %12#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %31 = constant %12#0 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %trueResult_8, %falseResult_9 = cond_br %30#0, %31 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i1>
    sink %trueResult_8 {handshake.name = "sink1"} : <i1>
    %32 = extui %falseResult_9 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i1> to <i32>
    %33 = mux %38#0 [%falseResult, %trueResult_16] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %34 = mux %38#1 [%32, %trueResult_18] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %35:3 = fork [3] %34 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i32>
    %36 = trunci %35#0 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i32> to <i10>
    %37 = trunci %35#1 {handshake.bb = 2 : ui32, handshake.name = "trunci3"} : <i32> to <i10>
    %result_10, %index_11 = control_merge [%falseResult_7, %trueResult_20]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %38:2 = fork [2] %index_11 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i1>
    %39 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %40 = constant %39 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 1000 : i32} : <>, <i32>
    %41 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %42 = constant %41 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 1 : i32} : <>, <i32>
    %43 = source {handshake.bb = 2 : ui32, handshake.name = "source6"} : <>
    %44 = constant %43 {handshake.bb = 2 : ui32, handshake.name = "constant4", value = -25 : i10} : <>, <i10>
    %45 = subi %44, %36 {handshake.bb = 2 : ui32, handshake.name = "subi1"} : <i10>
    %addressResult_12, %dataResult_13 = load[%45] %outputs_0#1 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load2"} : <i10>, <i32>, <i10>, <i32>
    %addressResult_14, %dataResult_15 = load[%37] %outputs#1 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load3"} : <i10>, <i32>, <i10>, <i32>
    %46 = muli %dataResult_13, %dataResult_15 {handshake.bb = 2 : ui32, handshake.name = "muli2"} : <i32>
    %47 = addi %33, %46 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %48 = addi %35#2, %42 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i32>
    %49:2 = fork [2] %48 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <i32>
    %50 = cmpi ne, %49#1, %40 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i32>
    %51:3 = fork [3] %50 {handshake.bb = 2 : ui32, handshake.name = "fork11"} : <i1>
    %trueResult_16, %falseResult_17 = cond_br %51#2, %47 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %51#1, %49#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_19 {handshake.name = "sink2"} : <i32>
    %trueResult_20, %falseResult_21 = cond_br %51#0, %result_10 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %52 = merge %falseResult_17 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %result_22, %index_23 = control_merge [%falseResult_21]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_23 {handshake.name = "sink3"} : <i1>
    %53:2 = fork [2] %result_22 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %52, %memEnd_1, %memEnd, %0#1 : <i32>, <>, <>, <>
  }
}

