module {
  handshake.func @collatz64(%arg0: !handshake.channel<i64>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["n", "start"], resNames = ["out0", "end"]} {
    %0:3 = fork [3] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg0 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i64>
    %2 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %3 = constant %2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1 : i64} : <>, <i64>
    %4 = cmpi eq, %1#1, %3 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i64>
    %5:3 = fork [3] %4 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %6 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %5#0, %6 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i1>
    %7 = extui %falseResult {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i1> to <i32>
    %8 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i1> to <i32>
    %trueResult_0, %falseResult_1 = cond_br %5#2, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %5#1, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i64>
    sink %trueResult_2 {handshake.name = "sink0"} : <i64>
    %9 = mux %14#0 [%falseResult_3, %falseResult_9] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i64>, <i64>] to <i64>
    %10:4 = fork [4] %9 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i64>
    %11 = trunci %10#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i64> to <i1>
    %12 = constant %19#0 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = true} : <>, <i1>
    %13 = mux %14#1 [%7, %falseResult_5] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%falseResult_1, %falseResult_7]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %14:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %15 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %16 = constant %15 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %17 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %18 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %19:2 = fork [2] %18 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <>
    %20 = constant %19#1 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 1 : i64} : <>, <i64>
    %21:4 = fork [4] %20 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i64>
    %22 = andi %11, %12 {handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i1>
    %23 = constant %17 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %24 = cmpi eq, %22, %23 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i1>
    %25 = shrsi %10#3, %21#3 {handshake.bb = 1 : ui32, handshake.name = "shrsi0"} : <i64>
    %26 = shli %10#2, %21#2 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i64>
    %27 = addi %10#1, %26 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i64>
    %28 = addi %27, %21#1 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i64>
    %29 = select %24[%25, %28] {handshake.bb = 1 : ui32, handshake.name = "select0"} : <i1>, <i64>
    %30:2 = fork [2] %29 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i64>
    %31 = addi %13, %16 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %32 = cmpi eq, %30#1, %21#0 {handshake.bb = 1 : ui32, handshake.name = "cmpi2"} : <i64>
    %33:3 = fork [3] %32 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i1>
    %trueResult_4, %falseResult_5 = cond_br %33#2, %31 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %33#1, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %trueResult_8, %falseResult_9 = cond_br %33#0, %30#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i64>
    sink %trueResult_8 {handshake.name = "sink1"} : <i64>
    %34 = mux %index_11 [%8, %trueResult_4] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result_10, %index_11 = control_merge [%trueResult_0, %trueResult_6]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    sink %result_10 {handshake.name = "sink2"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %34, %0#1 : <i32>, <>
  }
}

