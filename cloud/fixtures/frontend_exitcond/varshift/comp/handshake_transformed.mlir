module {
  handshake.func @varshift(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["x", "n", "start"], resNames = ["out0", "end"]} {
    %0:5 = fork [5] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2 = constant %0#4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = cmpi sgt, %1#1, %2 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %4:5 = fork [5] %3 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %5 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %4#0, %5 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i1>
    sink %falseResult {handshake.name = "sink0"} : <i1>
    %6 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i1> to <i32>
    %7 = constant %0#1 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = -607000171 : i31} : <>, <i31>
    %trueResult_0, %falseResult_1 = cond_br %4#1, %7 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i31>
    %8 = extui %falseResult_1 {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i31> to <i32>
    %9 = extui %trueResult_0 {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i31> to <i32>
    %trueResult_2, %falseResult_3 = cond_br %4#4, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    sink %falseResult_3 {handshake.name = "sink1"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %4#3, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %falseResult_5 {handshake.name = "sink2"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %4#2, %0#3 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %10 = mux %18#0 [%6, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %11:2 = fork [2] %10 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %12 = mux %18#1 [%9, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %13:3 = fork [3] %12 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %14 = mux %18#2 [%trueResult_2, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %15:2 = fork [2] %14 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %16 = mux %18#3 [%trueResult_4, %trueResult_14] {handshake.bb = 1 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %17:2 = fork [2] %16 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i32>
    %result, %index = control_merge [%trueResult_6, %trueResult_16]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %18:4 = fork [4] %index {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i1>
    %19 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %20 = constant %19 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %21 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %22 = constant %21 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 31 : i32} : <>, <i32>
    %23 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %24 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %25 = constant %24 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 27 : i32} : <>, <i32>
    %26 = shrui %13#2, %25 {handshake.bb = 1 : ui32, handshake.name = "shrui0"} : <i32>
    %27:3 = fork [3] %26 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i32>
    %28 = trunci %27#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i3>
    %29 = constant %23 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = -1 : i3} : <>, <i3>
    %30 = andi %28, %29 {handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i3>
    %31 = extui %30 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i3> to <i32>
    %32 = shli %13#1, %31 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %33 = shrui %15#1, %27#2 {handshake.bb = 1 : ui32, handshake.name = "shrui1"} : <i32>
    %34 = xori %32, %33 {handshake.bb = 1 : ui32, handshake.name = "xori0"} : <i32>
    %35 = xori %27#1, %22 {handshake.bb = 1 : ui32, handshake.name = "xori1"} : <i32>
    %36 = shrsi %13#0, %35 {handshake.bb = 1 : ui32, handshake.name = "shrsi0"} : <i32>
    %37 = xori %34, %36 {handshake.bb = 1 : ui32, handshake.name = "xori2"} : <i32>
    %38 = xori %37, %11#1 {handshake.bb = 1 : ui32, handshake.name = "xori3"} : <i32>
    %39 = addi %11#0, %20 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %40:2 = fork [2] %39 {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <i32>
    %41 = cmpi ne, %40#1, %17#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %42:5 = fork [5] %41 {handshake.bb = 1 : ui32, handshake.name = "fork10"} : <i1>
    %trueResult_8, %falseResult_9 = cond_br %42#4, %40#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_9 {handshake.name = "sink3"} : <i32>
    %trueResult_10, %falseResult_11 = cond_br %42#3, %38 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %42#2, %15#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    sink %falseResult_13 {handshake.name = "sink4"} : <i32>
    %trueResult_14, %falseResult_15 = cond_br %42#1, %17#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    sink %falseResult_15 {handshake.name = "sink5"} : <i32>
    %trueResult_16, %falseResult_17 = cond_br %42#0, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %43 = mux %index_19 [%8, %falseResult_11] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %result_18, %index_19 = control_merge [%falseResult_7, %falseResult_17]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    sink %result_18 {handshake.name = "sink6"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %43, %0#2 : <i32>, <>
  }
}

