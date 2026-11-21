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
    %11 = extui %10 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i1> to <i32>
    %12 = br %7 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i16>
    %13 = extui %12 {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i16> to <i32>
    %14 = br %8 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i16>
    %15 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %16 = mux %22#1 [%11, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %17 = mux %22#2 [%13, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %18:2 = fork [2] %17 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i32>
    %19 = mux %22#0 [%14, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i16>, <i16>] to <i16>
    %20:2 = fork [2] %19 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i16>
    %21 = extui %20#1 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i16> to <i32>
    %result, %index = control_merge [%15, %trueResult_14]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %22:3 = fork [3] %index {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %23 = cmpi eq, %18#1, %21 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %24:4 = fork [4] %23 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i1>
    %trueResult, %falseResult = cond_br %24#3, %16 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %24#2, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %24#0, %20#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i16>
    sink %trueResult_2 {handshake.name = "sink0"} : <i16>
    %trueResult_4, %falseResult_5 = cond_br %24#1, %18#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %trueResult_4 {handshake.name = "sink1"} : <i32>
    %25 = merge %falseResult_3 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i16>
    %26 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %27 = merge %falseResult_5 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %28:2 = fork [2] %27 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i32>
    %29 = trunci %28#0 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i32> to <i1>
    %30 = constant %35#0 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = true} : <>, <i1>
    %result_6, %index_7 = control_merge [%falseResult_1]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_7 {handshake.name = "sink2"} : <i1>
    %31:3 = fork [3] %result_6 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <>
    %32 = constant %31#2 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 256 : i32} : <>, <i32>
    %33 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %34 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %35:2 = fork [2] %34 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <>
    %36 = constant %35#1 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %37:2 = fork [2] %36 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i32>
    %38 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %39:2 = fork [2] %38 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <>
    %40 = shrui %28#1, %37#1 {handshake.bb = 2 : ui32, handshake.name = "shrui0"} : <i32>
    %41 = andi %29, %30 {handshake.bb = 2 : ui32, handshake.name = "andi2"} : <i1>
    %42 = constant %39#0 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = false} : <>, <i1>
    %43 = cmpi eq, %41, %42 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i1>
    %44 = constant %39#1 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 0 : i16} : <>, <i16>
    %45 = constant %33 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = -19456 : i16} : <>, <i16>
    %46 = select %43[%44, %45] {handshake.bb = 2 : ui32, handshake.name = "select0"} : <i1>, <i16>
    %47 = extui %46 {handshake.bb = 2 : ui32, handshake.name = "extui3"} : <i16> to <i32>
    %48 = xori %40, %47 {handshake.bb = 2 : ui32, handshake.name = "xori0"} : <i32>
    %49 = addi %26, %37#0 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %50:2 = fork [2] %49 {handshake.bb = 2 : ui32, handshake.name = "fork11"} : <i32>
    %51 = cmpi ne, %50#1, %32 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i32>
    %52:5 = fork [5] %51 {handshake.bb = 2 : ui32, handshake.name = "fork12"} : <i1>
    %trueResult_8, %falseResult_9 = cond_br %52#4, %50#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    sink %falseResult_9 {handshake.name = "sink3"} : <i32>
    %trueResult_10, %falseResult_11 = cond_br %52#3, %48 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_11 {handshake.name = "sink4"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %52#0, %25 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i16>
    sink %falseResult_13 {handshake.name = "sink5"} : <i16>
    %trueResult_14, %falseResult_15 = cond_br %52#2, %31#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %53 = constant %31#0 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = -256 : i9} : <>, <i9>
    %trueResult_16, %falseResult_17 = cond_br %52#1, %53 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <i9>
    sink %trueResult_16 {handshake.name = "sink6"} : <i9>
    %54 = extui %falseResult_17 {handshake.bb = 2 : ui32, handshake.name = "extui4"} : <i9> to <i32>
    %55 = mux %index_19 [%trueResult, %54] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_18, %index_19 = control_merge [%trueResult_0, %falseResult_15]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    sink %result_18 {handshake.name = "sink7"} : <>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %55, %0#1 : <i32>, <>
  }
}

