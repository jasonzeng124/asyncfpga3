module {
  handshake.func @fill(%arg0: memref<32xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "n", "x", "a_start", "start"], resNames = ["out0", "a_end", "end"]} {
    %0:5 = fork [5] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %memEnd = mem_controller[%arg0 : memref<32xi32>] %arg3 (%23, %addressResult, %dataResult) %result_20 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i5>, !handshake.channel<i32>) -> ()
    %2 = constant %0#4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = cmpi sgt, %1#1, %2 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %4:5 = fork [5] %3 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %5 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %4#0, %5 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i1>
    %6 = extui %falseResult {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i1> to <i32>
    %7 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i1> to <i32>
    %8:2 = fork [2] %7 {handshake.bb = 0 : ui32, handshake.name = "fork3"} : <i32>
    %9 = constant %0#1 {handshake.bb = 0 : ui32, handshake.name = "constant5", value = true} : <>, <i1>
    %trueResult_0, %falseResult_1 = cond_br %4#1, %9 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i1>
    sink %falseResult_1 {handshake.name = "sink0"} : <i1>
    %10 = extsi %trueResult_0 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i1> to <i2>
    %11 = extui %10 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i2> to <i5>
    %trueResult_2, %falseResult_3 = cond_br %4#4, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    sink %falseResult_3 {handshake.name = "sink1"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %4#3, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %falseResult_5 {handshake.name = "sink2"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %4#2, %0#3 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %12 = mux %21#1 [%8#0, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %13:2 = fork [2] %12 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %14 = mux %21#0 [%11, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i5>, <i5>] to <i5>
    %15:2 = fork [2] %14 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i5>
    %16 = mux %21#2 [%trueResult_2, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %17:2 = fork [2] %16 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i32>
    %18 = mux %21#3 [%8#1, %trueResult_14] {handshake.bb = 1 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %19 = mux %21#4 [%trueResult_4, %trueResult_16] {handshake.bb = 1 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %20:2 = fork [2] %19 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i32>
    %result, %index = control_merge [%trueResult_6, %trueResult_18]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %21:5 = fork [5] %index {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i1>
    %22:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <>
    %23 = constant %22#0 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %24 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %25 = constant %24 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %26 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %27 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %28 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %29 = constant %28 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 5 : i32} : <>, <i32>
    %30 = source {handshake.bb = 1 : ui32, handshake.name = "source4"} : <>
    %31 = constant %30 {handshake.bb = 1 : ui32, handshake.name = "constant10", value = 3 : i32} : <>, <i32>
    %32 = shli %17#1, %29 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %33 = xori %17#0, %32 {handshake.bb = 1 : ui32, handshake.name = "xori0"} : <i32>
    %34 = addi %33, %13#1 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %35:3 = fork [3] %34 {handshake.bb = 1 : ui32, handshake.name = "fork10"} : <i32>
    %addressResult, %dataResult = store[%15#1] %35#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store0"} : <i5>, <i32>, <i5>, <i32>
    %36 = constant %27 {handshake.bb = 1 : ui32, handshake.name = "constant11", value = 7 : i5} : <>, <i5>
    %37 = addi %15#0, %36 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i5>
    %38 = constant %26 {handshake.bb = 1 : ui32, handshake.name = "constant12", value = -1 : i5} : <>, <i5>
    %39 = andi %37, %38 {handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i5>
    %40 = shrsi %35#2, %31 {handshake.bb = 1 : ui32, handshake.name = "shrsi0"} : <i32>
    %41 = addi %18, %40 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %42 = addi %13#0, %25 {handshake.bb = 1 : ui32, handshake.name = "addi3"} : <i32>
    %43:2 = fork [2] %42 {handshake.bb = 1 : ui32, handshake.name = "fork11"} : <i32>
    %44 = cmpi ne, %43#1, %20#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %45:6 = fork [6] %44 {handshake.bb = 1 : ui32, handshake.name = "fork12"} : <i1>
    %trueResult_8, %falseResult_9 = cond_br %45#5, %43#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_9 {handshake.name = "sink3"} : <i32>
    %trueResult_10, %falseResult_11 = cond_br %45#0, %39 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i5>
    sink %falseResult_11 {handshake.name = "sink4"} : <i5>
    %trueResult_12, %falseResult_13 = cond_br %45#4, %35#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    sink %falseResult_13 {handshake.name = "sink5"} : <i32>
    %trueResult_14, %falseResult_15 = cond_br %45#3, %41 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %45#2, %20#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    sink %falseResult_17 {handshake.name = "sink6"} : <i32>
    %trueResult_18, %falseResult_19 = cond_br %45#1, %22#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br12"} : <i1>, <>
    %46 = mux %index_21 [%6, %falseResult_15] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %result_20, %index_21 = control_merge [%falseResult_7, %falseResult_19]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %46, %memEnd, %0#2 : <i32>, <>, <>
  }
}

