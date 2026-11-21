module {
  handshake.func @sum3(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["a", "b", "n", "start"], resNames = ["out0", "end"]} {
    %0:4 = fork [4] %arg3 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = cmpi sgt, %1#1, %2 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %4:5 = fork [5] %3 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %5 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %4#0, %5 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i1>
    sink %falseResult {handshake.name = "sink0"} : <i1>
    %6 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i1> to <i32>
    %trueResult_0, %falseResult_1 = cond_br %4#4, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %4#3, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    sink %falseResult_3 {handshake.name = "sink1"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %4#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %falseResult_5 {handshake.name = "sink2"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %4#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %7 = mux %14#0 [%6, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %8:2 = fork [2] %7 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %9 = mux %14#1 [%trueResult_0, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %10 = mux %14#2 [%trueResult_2, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %11:2 = fork [2] %10 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %12 = mux %14#3 [%trueResult_4, %trueResult_14] {handshake.bb = 1 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %13:2 = fork [2] %12 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %result, %index = control_merge [%trueResult_6, %trueResult_16]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %14:4 = fork [4] %index {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i1>
    %15 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %16 = constant %15 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %17 = xori %9, %11#1 {handshake.bb = 1 : ui32, handshake.name = "xori0"} : <i32>
    %18 = addi %17, %8#1 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %19 = addi %8#0, %16 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %20:2 = fork [2] %19 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i32>
    %21 = cmpi slt, %20#1, %13#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %22:5 = fork [5] %21 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i1>
    %trueResult_8, %falseResult_9 = cond_br %22#4, %20#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_9 {handshake.name = "sink3"} : <i32>
    %trueResult_10, %falseResult_11 = cond_br %22#3, %18 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %22#2, %11#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    sink %falseResult_13 {handshake.name = "sink4"} : <i32>
    %trueResult_14, %falseResult_15 = cond_br %22#1, %13#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    sink %falseResult_15 {handshake.name = "sink5"} : <i32>
    %trueResult_16, %falseResult_17 = cond_br %22#0, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %23 = mux %index_19 [%falseResult_1, %falseResult_11] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %result_18, %index_19 = control_merge [%falseResult_7, %falseResult_17]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    sink %result_18 {handshake.name = "sink6"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %23, %0#1 : <i32>, <>
  }
}

