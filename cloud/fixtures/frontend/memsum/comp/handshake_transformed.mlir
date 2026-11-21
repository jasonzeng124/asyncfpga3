module {
  handshake.func @memsum(%arg0: memref<32xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "n", "a_start", "start"], resNames = ["out0", "a_end", "end"]} {
    %0:4 = fork [4] %arg3 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %outputs, %memEnd = mem_controller[%arg0 : memref<32xi32>] %arg2 (%addressResult) %result_12 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i5>) -> !handshake.channel<i32>
    %2 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = cmpi sgt, %1#1, %2 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %4:3 = fork [3] %3 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %5 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %4#0, %5 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i1>
    %6:2 = fork [2] %trueResult {handshake.bb = 0 : ui32, handshake.name = "fork3"} : <i1>
    %7 = extui %falseResult {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i1> to <i32>
    %8 = extui %6#1 {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i1> to <i32>
    %9 = extui %6#0 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i1> to <i5>
    %trueResult_0, %falseResult_1 = cond_br %4#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    sink %falseResult_1 {handshake.name = "sink0"} : <i32>
    %trueResult_2, %falseResult_3 = cond_br %4#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %10 = mux %19#0 [%9, %trueResult_4] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i5>, <i5>] to <i5>
    %11:3 = fork [3] %10 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i5>
    %12 = extui %11#1 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i5> to <i6>
    %13 = constant %22#0 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i6} : <>, <i6>
    %14 = extui %11#2 {handshake.bb = 1 : ui32, handshake.name = "extui5"} : <i5> to <i6>
    %15 = constant %22#1 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 1 : i6} : <>, <i6>
    %16 = mux %19#1 [%8, %trueResult_6] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %17 = mux %19#2 [%trueResult_0, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %18:2 = fork [2] %17 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %result, %index = control_merge [%trueResult_2, %trueResult_10]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %19:3 = fork [3] %index {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i1>
    %20 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %21 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %22:2 = fork [2] %21 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <>
    %addressResult, %dataResult = load[%11#0] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i5>, <i32>, <i5>, <i32>
    %23 = addi %14, %15 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i6>
    %24 = extui %23 {handshake.bb = 1 : ui32, handshake.name = "extui6"} : <i6> to <i32>
    %25 = muli %dataResult, %24 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %26 = addi %16, %25 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %27 = addi %12, %13 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i6>
    %28:3 = fork [3] %27 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i6>
    %29 = trunci %28#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i6> to <i5>
    %30 = extui %28#2 {handshake.bb = 1 : ui32, handshake.name = "extui7"} : <i6> to <i32>
    %31 = cmpi slt, %30, %18#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %32 = constant %20 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = -32 : i6} : <>, <i6>
    %33 = cmpi ult, %28#1, %32 {handshake.bb = 1 : ui32, handshake.name = "cmpi2"} : <i6>
    %34 = andi %31, %33 {handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i1>
    %35:4 = fork [4] %34 {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult_4, %falseResult_5 = cond_br %35#0, %29 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i5>
    sink %falseResult_5 {handshake.name = "sink1"} : <i5>
    %trueResult_6, %falseResult_7 = cond_br %35#3, %26 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %35#2, %18#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_9 {handshake.name = "sink2"} : <i32>
    %trueResult_10, %falseResult_11 = cond_br %35#1, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %36 = mux %index_13 [%7, %falseResult_7] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_12, %index_13 = control_merge [%falseResult_3, %falseResult_11]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %36, %memEnd, %0#1 : <i32>, <>, <>
  }
}

