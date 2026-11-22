module {
  handshake.func @fold64(%arg0: !handshake.channel<i64>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["v", "start"], resNames = ["out0", "end"]} {
    %0:5 = fork [5] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg0 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i64>
    %2 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %3 = trunci %1#0 {handshake.bb = 0 : ui32, handshake.name = "trunci2"} : <i64> to <i8>
    %4 = constant %2 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = -1 : i8} : <>, <i8>
    %5 = andi %3, %4 {handshake.bb = 0 : ui32, handshake.name = "andi0"} : <i8>
    %6:2 = fork [2] %5 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i8>
    %7 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant4", value = 0 : i8} : <>, <i8>
    %8 = cmpi ugt, %6#1, %7 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i8>
    %9:5 = fork [5] %8 {handshake.bb = 0 : ui32, handshake.name = "fork3"} : <i1>
    %10 = constant %0#1 {handshake.bb = 0 : ui32, handshake.name = "constant5", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %9#4, %10 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i1>
    sink %falseResult {handshake.name = "sink0"} : <i1>
    %11 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i1> to <i32>
    %trueResult_0, %falseResult_1 = cond_br %9#1, %1#1 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i64>
    sink %falseResult_1 {handshake.name = "sink1"} : <i64>
    %12 = constant %0#2 {handshake.bb = 0 : ui32, handshake.name = "constant6", value = -62129658859368977 : i57} : <>, <i57>
    %trueResult_2, %falseResult_3 = cond_br %9#3, %12 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i57>
    %13 = extui %falseResult_3 {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i57> to <i64>
    %14 = extui %trueResult_2 {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i57> to <i64>
    %trueResult_4, %falseResult_5 = cond_br %9#0, %6#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i8>
    sink %falseResult_5 {handshake.name = "sink2"} : <i8>
    %trueResult_6, %falseResult_7 = cond_br %9#2, %0#4 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %15 = mux %23#1 [%11, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %16 = mux %23#2 [%trueResult_0, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i64>, <i64>] to <i64>
    %17:5 = fork [5] %16 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i64>
    %18 = mux %23#3 [%14, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i64>, <i64>] to <i64>
    %19:2 = fork [2] %18 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i64>
    %20 = mux %23#0 [%trueResult_4, %trueResult_14] {handshake.bb = 1 : ui32, handshake.name = "mux3"} : <i1>, [<i8>, <i8>] to <i8>
    %21:2 = fork [2] %20 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i8>
    %22 = extui %21#1 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i8> to <i32>
    %result, %index = control_merge [%trueResult_6, %trueResult_16]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %23:4 = fork [4] %index {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i1>
    %24 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %25 = constant %24 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 1 : i32} : <>, <i32>
    %26 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %27 = constant %26 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 11 : i64} : <>, <i64>
    %28 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %29 = constant %28 {handshake.bb = 1 : ui32, handshake.name = "constant10", value = 3 : i64} : <>, <i64>
    %30 = source {handshake.bb = 1 : ui32, handshake.name = "source4"} : <>
    %31 = constant %30 {handshake.bb = 1 : ui32, handshake.name = "constant11", value = 7 : i64} : <>, <i64>
    %32 = shli %19#1, %31 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i64>
    %33 = xori %17#4, %32 {handshake.bb = 1 : ui32, handshake.name = "xori0"} : <i64>
    %34 = addi %19#0, %33 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i64>
    %35:3 = fork [3] %34 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i64>
    %36 = cmpi ult, %35#2, %17#3 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i64>
    %37 = shrui %17#2, %29 {handshake.bb = 1 : ui32, handshake.name = "shrui0"} : <i64>
    %38 = addi %35#1, %37 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i64>
    %39 = select %36[%38, %35#0] {handshake.bb = 1 : ui32, handshake.name = "select0"} : <i1>, <i64>
    %40 = shrui %17#1, %27 {handshake.bb = 1 : ui32, handshake.name = "shrui1"} : <i64>
    %41 = xori %17#0, %40 {handshake.bb = 1 : ui32, handshake.name = "xori1"} : <i64>
    %42 = addi %15, %25 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %43:2 = fork [2] %42 {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <i32>
    %44 = cmpi ne, %43#1, %22 {handshake.bb = 1 : ui32, handshake.name = "cmpi2"} : <i32>
    %45:5 = fork [5] %44 {handshake.bb = 1 : ui32, handshake.name = "fork10"} : <i1>
    %trueResult_8, %falseResult_9 = cond_br %45#4, %43#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_9 {handshake.name = "sink3"} : <i32>
    %trueResult_10, %falseResult_11 = cond_br %45#3, %41 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i64>
    sink %falseResult_11 {handshake.name = "sink4"} : <i64>
    %trueResult_12, %falseResult_13 = cond_br %45#2, %39 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i64>
    %trueResult_14, %falseResult_15 = cond_br %45#0, %21#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i8>
    sink %falseResult_15 {handshake.name = "sink5"} : <i8>
    %trueResult_16, %falseResult_17 = cond_br %45#1, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %46 = mux %index_19 [%13, %falseResult_13] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i64>, <i64>] to <i64>
    %47:2 = fork [2] %46 {handshake.bb = 2 : ui32, handshake.name = "fork11"} : <i64>
    %result_18, %index_19 = control_merge [%falseResult_7, %falseResult_17]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    sink %result_18 {handshake.name = "sink6"} : <>
    %48 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %49 = constant %48 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 32 : i64} : <>, <i64>
    %50 = shrui %47#1, %49 {handshake.bb = 2 : ui32, handshake.name = "shrui2"} : <i64>
    %51 = xori %47#0, %50 {handshake.bb = 2 : ui32, handshake.name = "xori2"} : <i64>
    %52 = trunci %51 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i64> to <i32>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %52, %0#3 : <i32>, <>
  }
}

