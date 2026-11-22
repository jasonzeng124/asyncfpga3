module {
  handshake.func @xorshift(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["seed", "rounds", "start"], resNames = ["out0", "end"]} {
    %0:4 = fork [4] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = cmpi sgt, %1#1, %2 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %4:4 = fork [4] %3 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %5 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %4#0, %5 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i1>
    sink %falseResult {handshake.name = "sink0"} : <i1>
    %6 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i1> to <i32>
    %trueResult_0, %falseResult_1 = cond_br %4#3, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %4#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    sink %falseResult_3 {handshake.name = "sink1"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %4#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %7 = mux %12#0 [%6, %trueResult_6] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %8 = mux %12#1 [%trueResult_0, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %9:2 = fork [2] %8 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %10 = mux %12#2 [%trueResult_2, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %11:2 = fork [2] %10 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %result, %index = control_merge [%trueResult_4, %trueResult_12]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %12:3 = fork [3] %index {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i1>
    %13 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %14 = constant %13 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %15 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %16 = constant %15 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 5 : i32} : <>, <i32>
    %17 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %18 = constant %17 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 17 : i32} : <>, <i32>
    %19 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %20 = constant %19 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 13 : i32} : <>, <i32>
    %21 = shli %9#1, %20 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %22 = xori %9#0, %21 {handshake.bb = 1 : ui32, handshake.name = "xori0"} : <i32>
    %23:2 = fork [2] %22 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i32>
    %24 = shrui %23#1, %18 {handshake.bb = 1 : ui32, handshake.name = "shrui0"} : <i32>
    %25 = xori %23#0, %24 {handshake.bb = 1 : ui32, handshake.name = "xori1"} : <i32>
    %26:2 = fork [2] %25 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i32>
    %27 = shli %26#1, %16 {handshake.bb = 1 : ui32, handshake.name = "shli1"} : <i32>
    %28 = xori %26#0, %27 {handshake.bb = 1 : ui32, handshake.name = "xori2"} : <i32>
    %29 = addi %7, %14 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %30:2 = fork [2] %29 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i32>
    %31 = cmpi slt, %30#1, %11#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %32:4 = fork [4] %31 {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult_6, %falseResult_7 = cond_br %32#3, %30#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    sink %falseResult_7 {handshake.name = "sink2"} : <i32>
    %trueResult_8, %falseResult_9 = cond_br %32#2, %28 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %32#1, %11#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    sink %falseResult_11 {handshake.name = "sink3"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %32#0, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %33 = mux %index_15 [%falseResult_1, %falseResult_9] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_14, %index_15 = control_merge [%falseResult_5, %falseResult_13]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    sink %result_14 {handshake.name = "sink4"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %33, %0#1 : <i32>, <>
  }
}

