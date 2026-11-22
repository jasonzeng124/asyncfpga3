module {
  handshake.func @iterative_sqrt(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["n", "start"], resNames = ["out0", "end"]} {
    %0:4 = fork [4] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg0 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = cmpi slt, %1#1, %2 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %4:3 = fork [3] %3 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %trueResult, %falseResult = cond_br %4#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %5:2 = fork [2] %falseResult {handshake.bb = 0 : ui32, handshake.name = "fork3"} : <i32>
    %trueResult_0, %falseResult_1 = cond_br %4#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %6 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %trueResult_2, %falseResult_3 = cond_br %4#0, %6 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i1>
    sink %trueResult_2 {handshake.name = "sink0"} : <i1>
    %7 = extui %falseResult_3 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i1> to <i32>
    %8 = mux %14#0 [%5#1, %falseResult_17] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %9:2 = fork [2] %8 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %10 = mux %14#1 [%7, %falseResult_21] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %11:2 = fork [2] %10 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %12 = mux %14#2 [%5#0, %falseResult_23] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %13:2 = fork [2] %12 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i32>
    %result, %index = control_merge [%falseResult_1, %falseResult_19]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %14:3 = fork [3] %index {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i1>
    %15 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %16 = constant %15 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %17 = addi %11#1, %9#1 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %18 = shrsi %17, %16 {handshake.bb = 1 : ui32, handshake.name = "shrsi0"} : <i32>
    %19:3 = fork [3] %18 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i32>
    %20 = muli %19#1, %19#2 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %21 = cmpi eq, %20, %13#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %22:5 = fork [5] %21 {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult_4, %falseResult_5 = cond_br %22#4, %19#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %22#3, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %trueResult_8, %falseResult_9 = cond_br %22#2, %13#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    sink %trueResult_8 {handshake.name = "sink1"} : <i32>
    %trueResult_10, %falseResult_11 = cond_br %22#1, %9#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    sink %trueResult_10 {handshake.name = "sink2"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %22#0, %11#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    sink %trueResult_12 {handshake.name = "sink3"} : <i32>
    %23 = merge %falseResult_9 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %24:2 = fork [2] %23 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <i32>
    %25 = merge %falseResult_11 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %26 = merge %falseResult_13 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %27 = merge %falseResult_5 {handshake.bb = 2 : ui32, handshake.name = "merge3"} : <i32>
    %28:4 = fork [4] %27 {handshake.bb = 2 : ui32, handshake.name = "fork11"} : <i32>
    %result_14, %index_15 = control_merge [%falseResult_7]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_15 {handshake.name = "sink4"} : <i1>
    %29 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %30 = constant %29 {handshake.bb = 2 : ui32, handshake.name = "constant4", value = -1 : i32} : <>, <i32>
    %31 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %32 = constant %31 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %33 = muli %28#2, %28#3 {handshake.bb = 2 : ui32, handshake.name = "muli1"} : <i32>
    %34 = cmpi slt, %33, %24#1 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i32>
    %35:2 = fork [2] %34 {handshake.bb = 2 : ui32, handshake.name = "fork12"} : <i1>
    %36 = addi %28#1, %32 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %37 = addi %28#0, %30 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %38 = select %35#1[%36, %26] {handshake.bb = 2 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %39:2 = fork [2] %38 {handshake.bb = 2 : ui32, handshake.name = "fork13"} : <i32>
    %40 = select %35#0[%25, %37] {handshake.bb = 2 : ui32, handshake.name = "select1"} : <i1>, <i32>
    %41:2 = fork [2] %40 {handshake.bb = 2 : ui32, handshake.name = "fork14"} : <i32>
    %42 = cmpi sgt, %39#1, %41#1 {handshake.bb = 2 : ui32, handshake.name = "cmpi3"} : <i32>
    %43:4 = fork [4] %42 {handshake.bb = 2 : ui32, handshake.name = "fork15"} : <i1>
    %trueResult_16, %falseResult_17 = cond_br %43#3, %41#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %43#2, %result_14 {handshake.bb = 2 : ui32, handshake.name = "cond_br12"} : <i1>, <>
    %trueResult_20, %falseResult_21 = cond_br %43#1, %39#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    sink %trueResult_20 {handshake.name = "sink5"} : <i32>
    %trueResult_22, %falseResult_23 = cond_br %43#0, %24#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    sink %trueResult_22 {handshake.name = "sink6"} : <i32>
    %44 = mux %index_25 [%trueResult, %trueResult_4, %trueResult_16] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %result_24, %index_25 = control_merge [%trueResult_0, %trueResult_6, %trueResult_18]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>, <>] to <>, <i2>
    sink %result_24 {handshake.name = "sink7"} : <>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %44, %0#1 : <i32>, <>
  }
}

