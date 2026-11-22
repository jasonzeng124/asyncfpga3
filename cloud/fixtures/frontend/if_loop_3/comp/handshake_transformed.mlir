module {
  handshake.func @if_loop_3(%arg0: memref<100xi32>, %arg1: memref<100xi32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "n", "a_start", "b_start", "start"], resNames = ["out0", "a_end", "b_end", "end"]} {
    %0:5 = fork [5] %arg5 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %outputs, %memEnd = mem_controller[%arg1 : memref<100xi32>] %arg4 (%addressResult_8) %46#1 {connectedBlocks = [1 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i7>) -> !handshake.channel<i32>
    %outputs_0, %memEnd_1 = mem_controller[%arg0 : memref<100xi32>] %arg3 (%addressResult) %46#0 {connectedBlocks = [1 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i7>) -> !handshake.channel<i32>
    %2 = constant %0#4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = cmpi sgt, %1#1, %2 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %4:4 = fork [4] %3 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %5 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %4#0, %5 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i1>
    sink %falseResult {handshake.name = "sink0"} : <i1>
    %6 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i1> to <i32>
    %7 = constant %0#1 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = -24 : i6} : <>, <i6>
    %trueResult_2, %falseResult_3 = cond_br %4#1, %7 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i6>
    %8 = extsi %falseResult_3 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i6> to <i10>
    %9 = extsi %trueResult_2 {handshake.bb = 0 : ui32, handshake.name = "extsi1"} : <i6> to <i10>
    %10 = extui %8 {handshake.bb = 0 : ui32, handshake.name = "extui3"} : <i10> to <i32>
    %11 = extui %9 {handshake.bb = 0 : ui32, handshake.name = "extui4"} : <i10> to <i32>
    %trueResult_4, %falseResult_5 = cond_br %4#3, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %falseResult_5 {handshake.name = "sink1"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %4#2, %0#3 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %12 = mux %18#0 [%6, %trueResult_24] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %13:3 = fork [3] %12 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %14 = trunci %13#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i7>
    %15 = trunci %13#1 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i7>
    %16 = mux %18#1 [%11, %trueResult_26] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %17 = mux %18#2 [%trueResult_4, %trueResult_28] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_6, %trueResult_30]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %18:3 = fork [3] %index {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %19 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %20 = constant %19 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = -1 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%15] %outputs_0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i7>, <i32>, <i7>, <i32>
    %addressResult_8, %dataResult_9 = load[%14] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i7>, <i32>, <i7>, <i32>
    %21 = subi %dataResult, %dataResult_9 {handshake.bb = 1 : ui32, handshake.name = "subi0"} : <i32>
    %22:2 = fork [2] %21 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %23 = cmpi sgt, %22#1, %20 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %24:5 = fork [5] %23 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i1>
    %trueResult_10, %falseResult_11 = cond_br %24#4, %17 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %24#3, %13#2 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %24#2, %16 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %24#1, %22#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    sink %falseResult_17 {handshake.name = "sink2"} : <i32>
    %trueResult_18, %falseResult_19 = cond_br %24#0, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %25 = merge %trueResult_10 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %26 = merge %trueResult_12 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %27 = merge %trueResult_14 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %28 = merge %trueResult_16 {handshake.bb = 2 : ui32, handshake.name = "merge3"} : <i32>
    %result_20, %index_21 = control_merge [%trueResult_18]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_21 {handshake.name = "sink3"} : <i1>
    %29 = divsi %27, %28 {handshake.bb = 2 : ui32, handshake.name = "divsi0"} : <i32>
    %30 = br %29 {handshake.bb = 2 : ui32, handshake.name = "br1"} : <i32>
    %31 = br %25 {handshake.bb = 2 : ui32, handshake.name = "br2"} : <i32>
    %32 = br %26 {handshake.bb = 2 : ui32, handshake.name = "br3"} : <i32>
    %33 = br %result_20 {handshake.bb = 2 : ui32, handshake.name = "br4"} : <>
    %34 = mux %38#0 [%falseResult_15, %30] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %35 = mux %38#1 [%falseResult_11, %31] {handshake.bb = 3 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %36:2 = fork [2] %35 {handshake.bb = 3 : ui32, handshake.name = "fork7"} : <i32>
    %37 = mux %38#2 [%falseResult_13, %32] {handshake.bb = 3 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %result_22, %index_23 = control_merge [%falseResult_19, %33]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %38:3 = fork [3] %index_23 {handshake.bb = 3 : ui32, handshake.name = "fork8"} : <i1>
    %39 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %40 = constant %39 {handshake.bb = 3 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %41 = addi %37, %40 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i32>
    %42:2 = fork [2] %41 {handshake.bb = 3 : ui32, handshake.name = "fork9"} : <i32>
    %43 = cmpi slt, %42#1, %36#1 {handshake.bb = 3 : ui32, handshake.name = "cmpi2"} : <i32>
    %44:4 = fork [4] %43 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i1>
    %trueResult_24, %falseResult_25 = cond_br %44#3, %42#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    sink %falseResult_25 {handshake.name = "sink4"} : <i32>
    %trueResult_26, %falseResult_27 = cond_br %44#2, %34 {handshake.bb = 3 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_28, %falseResult_29 = cond_br %44#1, %36#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    sink %falseResult_29 {handshake.name = "sink5"} : <i32>
    %trueResult_30, %falseResult_31 = cond_br %44#0, %result_22 {handshake.bb = 3 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %45 = mux %index_33 [%10, %falseResult_27] {handshake.bb = 4 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %result_32, %index_33 = control_merge [%falseResult_7, %falseResult_31]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %46:2 = fork [2] %result_32 {handshake.bb = 4 : ui32, handshake.name = "fork11"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %45, %memEnd_1, %memEnd, %0#2 : <i32>, <>, <>, <>
  }
}

