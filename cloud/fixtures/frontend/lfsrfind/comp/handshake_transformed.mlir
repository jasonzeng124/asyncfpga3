module {
  handshake.func @lfsrfind(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["seed", "key", "start"], resNames = ["out0", "end"]} {
    %0:3 = fork [3] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1 = trunci %arg0 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i32> to <i16>
    %2 = constant %6#0 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = -1 : i16} : <>, <i16>
    %3 = trunci %arg1 {handshake.bb = 0 : ui32, handshake.name = "trunci1"} : <i32> to <i16>
    %4 = constant %6#1 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = -1 : i16} : <>, <i16>
    %5 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %6:2 = fork [2] %5 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <>
    %7 = andi %1, %2 {handshake.bb = 0 : ui32, handshake.name = "andi0"} : <i16>
    %8 = andi %3, %4 {handshake.bb = 0 : ui32, handshake.name = "andi1"} : <i16>
    %9 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %10 = br %9 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %11 = extui %10 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i1> to <i8>
    %12 = br %7 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i16>
    %13 = extui %12 {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i16> to <i32>
    %14 = br %8 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i16>
    %15 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %16 = mux %22#1 [%11, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i8>, <i8>] to <i8>
    %17 = mux %22#2 [%13, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %18:2 = fork [2] %17 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i32>
    %19 = mux %22#0 [%14, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i16>, <i16>] to <i16>
    %20:2 = fork [2] %19 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i16>
    %21 = extui %20#1 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i16> to <i32>
    %result, %index = control_merge [%15, %trueResult_14]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %22:3 = fork [3] %index {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %23 = cmpi eq, %18#1, %21 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %24:4 = fork [4] %23 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i1>
    %trueResult, %falseResult = cond_br %24#1, %16 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i8>
    %25 = extui %trueResult {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i8> to <i9>
    %trueResult_0, %falseResult_1 = cond_br %24#3, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %24#0, %20#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i16>
    sink %trueResult_2 {handshake.name = "sink0"} : <i16>
    %trueResult_4, %falseResult_5 = cond_br %24#2, %18#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %trueResult_4 {handshake.name = "sink1"} : <i32>
    %26 = merge %falseResult_3 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i16>
    %27 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i8>
    %28 = extui %27 {handshake.bb = 2 : ui32, handshake.name = "extui4"} : <i8> to <i9>
    %29 = constant %37#0 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 1 : i9} : <>, <i9>
    %30 = merge %falseResult_5 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %31:2 = fork [2] %30 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i32>
    %32 = trunci %31#0 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i32> to <i1>
    %33 = constant %37#1 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = true} : <>, <i1>
    %result_6, %index_7 = control_merge [%falseResult_1]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_7 {handshake.name = "sink2"} : <i1>
    %34:3 = fork [3] %result_6 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <>
    %35 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %36 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %37:3 = fork [3] %36 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <>
    %38 = constant %37#2 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %39 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %40:2 = fork [2] %39 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <>
    %41 = shrui %31#1, %38 {handshake.bb = 2 : ui32, handshake.name = "shrui0"} : <i32>
    %42 = andi %32, %33 {handshake.bb = 2 : ui32, handshake.name = "andi2"} : <i1>
    %43 = constant %40#0 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = false} : <>, <i1>
    %44 = cmpi eq, %42, %43 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i1>
    %45 = constant %40#1 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 0 : i16} : <>, <i16>
    %46 = constant %35 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = -19456 : i16} : <>, <i16>
    %47 = select %44[%45, %46] {handshake.bb = 2 : ui32, handshake.name = "select0"} : <i1>, <i16>
    %48 = extui %47 {handshake.bb = 2 : ui32, handshake.name = "extui5"} : <i16> to <i32>
    %49 = xori %41, %48 {handshake.bb = 2 : ui32, handshake.name = "xori0"} : <i32>
    %50 = addi %28, %29 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i9>
    %51:2 = fork [2] %50 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <i9>
    %52 = trunci %51#0 {handshake.bb = 2 : ui32, handshake.name = "trunci3"} : <i9> to <i8>
    %53 = constant %34#0 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = -256 : i9} : <>, <i9>
    %54 = cmpi ult, %51#1, %53 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i9>
    %55:5 = fork [5] %54 {handshake.bb = 2 : ui32, handshake.name = "fork11"} : <i1>
    %trueResult_8, %falseResult_9 = cond_br %55#0, %52 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i8>
    sink %falseResult_9 {handshake.name = "sink3"} : <i8>
    %trueResult_10, %falseResult_11 = cond_br %55#2, %49 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_11 {handshake.name = "sink4"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %55#1, %26 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i16>
    sink %falseResult_13 {handshake.name = "sink5"} : <i16>
    %trueResult_14, %falseResult_15 = cond_br %55#3, %34#2 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %56 = constant %34#1 {handshake.bb = 2 : ui32, handshake.name = "constant15", value = -256 : i9} : <>, <i9>
    %trueResult_16, %falseResult_17 = cond_br %55#4, %56 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <i9>
    sink %trueResult_16 {handshake.name = "sink6"} : <i9>
    %57 = mux %index_19 [%25, %falseResult_17] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i9>, <i9>] to <i9>
    %58 = extui %57 {handshake.bb = 3 : ui32, handshake.name = "extui6"} : <i9> to <i32>
    %result_18, %index_19 = control_merge [%trueResult_0, %falseResult_15]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    sink %result_18 {handshake.name = "sink7"} : <>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %58, %0#1 : <i32>, <>
  }
}

