module {
  handshake.func @pivot(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.channel<i32>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["x", "a", "n", "k", "x_start", "a_start", "start"], resNames = ["x_end", "a_end", "end"]} {
    %0:3 = fork [3] %arg6 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:3 = fork [3] %arg3 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2:2 = fork [2] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i32>
    %outputs, %memEnd = mem_controller[%arg1 : memref<1000xi32>] %arg5 (%addressResult_12) %32#1 {connectedBlocks = [1 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %outputs_0:2, %memEnd_1 = mem_controller[%arg0 : memref<1000xi32>] %arg4 (%24, %addressResult_14, %3#1, %3#2, %3#3) %32#0 {connectedBlocks = [1 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i10>, !handshake.channel<i10>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %3:4 = lsq[MC] (%23#0, %addressResult, %dataResult, %addressResult_10, %outputs_0#1)  {groupSizes = [2 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.channel<i10>, !handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i10>, !handshake.channel<i32>)
    %4 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %5 = constant %4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %6 = addi %1#2, %5 {handshake.bb = 0 : ui32, handshake.name = "addi0"} : <i32>
    %7 = cmpi slt, %1#1, %2#1 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %8:5 = fork [5] %7 {handshake.bb = 0 : ui32, handshake.name = "fork3"} : <i1>
    %trueResult, %falseResult = cond_br %8#4, %6 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    sink %falseResult {handshake.name = "sink0"} : <i32>
    %9 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant5", value = false} : <>, <i1>
    %trueResult_2, %falseResult_3 = cond_br %8#0, %9 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i1>
    sink %falseResult_3 {handshake.name = "sink1"} : <i1>
    %10 = extui %trueResult_2 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i1> to <i32>
    %trueResult_4, %falseResult_5 = cond_br %8#3, %2#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    sink %falseResult_5 {handshake.name = "sink2"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %8#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %falseResult_7 {handshake.name = "sink3"} : <i32>
    %trueResult_8, %falseResult_9 = cond_br %8#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %11 = mux %22#0 [%trueResult, %trueResult_16] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %12:4 = fork [4] %11 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %13 = trunci %12#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i10>
    %14 = trunci %12#1 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i10>
    %15 = mux %22#1 [%10, %trueResult_18] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %16 = mux %22#2 [%trueResult_4, %trueResult_20] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %17:2 = fork [2] %16 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %18 = mux %22#3 [%trueResult_6, %trueResult_22] {handshake.bb = 1 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %19:3 = fork [3] %18 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i32>
    %20 = trunci %19#0 {handshake.bb = 1 : ui32, handshake.name = "trunci2"} : <i32> to <i10>
    %21 = trunci %19#1 {handshake.bb = 1 : ui32, handshake.name = "trunci3"} : <i32> to <i10>
    %result, %index = control_merge [%trueResult_8, %trueResult_24]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %22:4 = fork [4] %index {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i1>
    %23:3 = fork [3] %result {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <>
    %24 = constant %23#1 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %25 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %26 = constant %25 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %addressResult, %dataResult = store[%21] %15 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store0"} : <i10>, <i32>, <i10>, <i32>
    %addressResult_10, %dataResult_11 = load[%20] %3#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load1"} : <i10>, <i32>, <i10>, <i32>
    %addressResult_12, %dataResult_13 = load[%14] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load2"} : <i10>, <i32>, <i10>, <i32>
    %addressResult_14, %dataResult_15 = load[%13] %outputs_0#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load3"} : <i10>, <i32>, <i10>, <i32>
    %27 = muli %dataResult_13, %dataResult_15 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %28 = subi %dataResult_11, %27 {handshake.bb = 1 : ui32, handshake.name = "subi0"} : <i32>
    %29 = addi %12#3, %26 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %30 = cmpi slt, %12#2, %17#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %31:5 = fork [5] %30 {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult_16, %falseResult_17 = cond_br %31#4, %29 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_17 {handshake.name = "sink4"} : <i32>
    %trueResult_18, %falseResult_19 = cond_br %31#3, %28 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    sink %falseResult_19 {handshake.name = "sink5"} : <i32>
    %trueResult_20, %falseResult_21 = cond_br %31#2, %17#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    sink %falseResult_21 {handshake.name = "sink6"} : <i32>
    %trueResult_22, %falseResult_23 = cond_br %31#1, %19#2 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    sink %falseResult_23 {handshake.name = "sink7"} : <i32>
    %trueResult_24, %falseResult_25 = cond_br %31#0, %23#2 {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %result_26, %index_27 = control_merge [%falseResult_9, %falseResult_25]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    sink %index_27 {handshake.name = "sink8"} : <i1>
    %32:2 = fork [2] %result_26 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %memEnd_1, %memEnd, %0#1 : <>, <>, <>
  }
}

