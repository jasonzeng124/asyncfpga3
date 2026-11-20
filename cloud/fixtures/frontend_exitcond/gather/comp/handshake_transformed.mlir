module {
  handshake.func @gather(%arg0: memref<32xi32>, %arg1: memref<32xi32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "n", "a_start", "b_start", "start"], resNames = ["out0", "a_end", "b_end", "end"]} {
    %0:4 = fork [4] %arg5 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %outputs, %memEnd = mem_controller[%arg1 : memref<32xi32>] %arg4 (%addressResult) %43#1 {connectedBlocks = [2 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i5>) -> !handshake.channel<i32>
    %outputs_0, %memEnd_1 = mem_controller[%arg0 : memref<32xi32>] %arg3 (%addressResult_8) %43#0 {connectedBlocks = [2 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i5>) -> !handshake.channel<i32>
    %2 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = cmpi sgt, %1#1, %2 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %4:3 = fork [3] %3 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %trueResult, %falseResult = cond_br %4#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    sink %falseResult {handshake.name = "sink0"} : <i32>
    %trueResult_2, %falseResult_3 = cond_br %4#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %5 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %trueResult_4, %falseResult_5 = cond_br %4#0, %5 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i1>
    sink %trueResult_4 {handshake.name = "sink1"} : <i1>
    %6 = extui %falseResult_5 {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i1> to <i32>
    %7 = merge %trueResult {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %result, %index = control_merge [%trueResult_2]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    sink %index {handshake.name = "sink2"} : <i1>
    %8:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <>
    %9 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %10 = constant %9 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %11 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %12 = constant %11 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 31 : i32} : <>, <i32>
    %13 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %14 = constant %13 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = -1 : i32} : <>, <i32>
    %15 = addi %7, %14 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %16 = minui %15, %12 {handshake.bb = 1 : ui32, handshake.name = "minui0"} : <i32>
    %17 = addi %16, %10 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %18 = constant %8#0 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = false} : <>, <i1>
    %19 = br %18 {handshake.bb = 1 : ui32, handshake.name = "br1"} : <i1>
    %20 = extui %19 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i1> to <i32>
    %21:2 = fork [2] %20 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %22 = br %17 {handshake.bb = 1 : ui32, handshake.name = "br2"} : <i32>
    %23 = br %8#1 {handshake.bb = 1 : ui32, handshake.name = "br3"} : <>
    %24 = mux %30#0 [%21#0, %trueResult_10] {handshake.bb = 2 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %25:3 = fork [3] %24 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i32>
    %26 = trunci %25#0 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i32> to <i5>
    %27 = mux %30#1 [%21#1, %trueResult_12] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %28 = mux %30#2 [%22, %trueResult_14] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %29:2 = fork [2] %28 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i32>
    %result_6, %index_7 = control_merge [%23, %trueResult_16]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %30:3 = fork [3] %index_7 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i1>
    %31 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %32 = constant %31 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 1 : i32} : <>, <i32>
    %33:2 = fork [2] %32 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i32>
    %addressResult, %dataResult = load[%26] %outputs {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i5>, <i32>, <i5>, <i32>
    %34 = trunci %dataResult {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i32> to <i5>
    %addressResult_8, %dataResult_9 = load[%34] %outputs_0 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i5>, <i32>, <i5>, <i32>
    %35 = addi %25#2, %33#1 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %36 = muli %dataResult_9, %35 {handshake.bb = 2 : ui32, handshake.name = "muli0"} : <i32>
    %37 = addi %27, %36 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i32>
    %38 = addi %25#1, %33#0 {handshake.bb = 2 : ui32, handshake.name = "addi4"} : <i32>
    %39:2 = fork [2] %38 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i32>
    %40 = cmpi ne, %39#1, %29#1 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i32>
    %41:4 = fork [4] %40 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <i1>
    %trueResult_10, %falseResult_11 = cond_br %41#3, %39#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %falseResult_11 {handshake.name = "sink3"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %41#2, %37 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %41#1, %29#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_15 {handshake.name = "sink4"} : <i32>
    %trueResult_16, %falseResult_17 = cond_br %41#0, %result_6 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %42 = mux %index_19 [%6, %falseResult_13] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_18, %index_19 = control_merge [%falseResult_3, %falseResult_17]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %43:2 = fork [2] %result_18 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %42, %memEnd_1, %memEnd, %0#1 : <i32>, <>, <>, <>
  }
}

