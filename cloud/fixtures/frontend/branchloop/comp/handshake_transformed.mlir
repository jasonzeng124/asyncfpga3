module {
  handshake.func @branchloop(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["n", "start"], resNames = ["out0", "end"]} {
    %0:3 = fork [3] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg0 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %3 = constant %2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %4 = cmpi sgt, %1#1, %3 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %5:3 = fork [3] %4 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %trueResult, %falseResult = cond_br %5#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %falseResult {handshake.name = "sink0"} : <i32>
    %6 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = false} : <>, <i1>
    %trueResult_0, %falseResult_1 = cond_br %5#0, %6 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <i1>
    %7 = extui %falseResult_1 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i1> to <i32>
    %8 = extui %trueResult_0 {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i1> to <i32>
    %trueResult_2, %falseResult_3 = cond_br %5#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %9 = mux %14#0 [%trueResult, %trueResult_32] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %10:2 = fork [2] %9 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %11 = trunci %10#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i1>
    %12 = constant %16 {handshake.bb = 1 : ui32, handshake.name = "constant11", value = true} : <>, <i1>
    %13 = mux %14#1 [%8, %trueResult_34] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_2, %trueResult_36]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %14:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %15 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %16 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %17 = andi %11, %12 {handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i1>
    %18 = constant %15 {handshake.bb = 1 : ui32, handshake.name = "constant12", value = false} : <>, <i1>
    %19 = cmpi eq, %17, %18 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i1>
    %20:3 = fork [3] %19 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i1>
    %trueResult_4, %falseResult_5 = cond_br %20#0, %10#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %20#1, %13 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %20#2, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %21 = merge %falseResult_5 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %22:2 = fork [2] %21 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i32>
    %23 = trunci %22#0 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i32> to <i2>
    %24 = constant %27#1 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = -1 : i2} : <>, <i2>
    %25 = merge %falseResult_7 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %result_10, %index_11 = control_merge [%falseResult_9]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_11 {handshake.name = "sink1"} : <i1>
    %26 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %27:2 = fork [2] %26 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <>
    %28 = andi %23, %24 {handshake.bb = 2 : ui32, handshake.name = "andi1"} : <i2>
    %29 = constant %27#0 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = -1 : i2} : <>, <i2>
    %30 = cmpi eq, %28, %29 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i2>
    %31:3 = fork [3] %30 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i1>
    %trueResult_12, %falseResult_13 = cond_br %31#0, %22#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %31#1, %25 {handshake.bb = 2 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %31#2, %result_10 {handshake.bb = 2 : ui32, handshake.name = "cond_br13"} : <i1>, <>
    %32 = mux %34#0 [%trueResult_12, %trueResult_20] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %33 = mux %34#1 [%trueResult_14, %trueResult_22] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_18, %index_19 = control_merge [%trueResult_16, %trueResult_24]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %34:2 = fork [2] %index_19 {handshake.bb = 3 : ui32, handshake.name = "fork9"} : <i1>
    %35 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %36:2 = fork [2] %35 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <>
    %37 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %38 = constant %37 {handshake.bb = 3 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %39:2 = fork [2] %38 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i32>
    %40 = shrsi %32, %39#1 {handshake.bb = 3 : ui32, handshake.name = "shrsi0"} : <i32>
    %41:2 = fork [2] %40 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <i32>
    %42 = trunci %41#0 {handshake.bb = 3 : ui32, handshake.name = "trunci2"} : <i32> to <i2>
    %43 = constant %36#1 {handshake.bb = 3 : ui32, handshake.name = "constant15", value = -1 : i2} : <>, <i2>
    %44 = addi %33, %39#0 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i32>
    %45 = andi %42, %43 {handshake.bb = 3 : ui32, handshake.name = "andi2"} : <i2>
    %46 = constant %36#0 {handshake.bb = 3 : ui32, handshake.name = "constant16", value = -1 : i2} : <>, <i2>
    %47 = cmpi eq, %45, %46 {handshake.bb = 3 : ui32, handshake.name = "cmpi3"} : <i2>
    %48:3 = fork [3] %47 {handshake.bb = 3 : ui32, handshake.name = "fork13"} : <i1>
    %trueResult_20, %falseResult_21 = cond_br %48#0, %41#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %48#1, %44 {handshake.bb = 3 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %48#2, %result_18 {handshake.bb = 3 : ui32, handshake.name = "cond_br16"} : <i1>, <>
    %49 = mux %51#0 [%falseResult_15, %falseResult_23] {handshake.bb = 4 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %50 = mux %51#1 [%falseResult_13, %falseResult_21] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %result_26, %index_27 = control_merge [%falseResult_17, %falseResult_25]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %51:2 = fork [2] %index_27 {handshake.bb = 4 : ui32, handshake.name = "fork14"} : <i1>
    %52 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %53 = constant %52 {handshake.bb = 4 : ui32, handshake.name = "constant8", value = 1 : i32} : <>, <i32>
    %54 = addi %50, %53 {handshake.bb = 4 : ui32, handshake.name = "addi1"} : <i32>
    %55 = br %49 {handshake.bb = 4 : ui32, handshake.name = "br2"} : <i32>
    %56 = br %54 {handshake.bb = 4 : ui32, handshake.name = "br3"} : <i32>
    %57 = br %result_26 {handshake.bb = 4 : ui32, handshake.name = "br4"} : <>
    %58 = merge %trueResult_4 {handshake.bb = 5 : ui32, handshake.name = "merge2"} : <i32>
    %59 = merge %trueResult_6 {handshake.bb = 5 : ui32, handshake.name = "merge3"} : <i32>
    %result_28, %index_29 = control_merge [%trueResult_8]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    sink %index_29 {handshake.name = "sink2"} : <i1>
    %60 = source {handshake.bb = 5 : ui32, handshake.name = "source7"} : <>
    %61 = constant %60 {handshake.bb = 5 : ui32, handshake.name = "constant9", value = 1 : i32} : <>, <i32>
    %62 = shrsi %58, %61 {handshake.bb = 5 : ui32, handshake.name = "shrsi1"} : <i32>
    %63 = br %59 {handshake.bb = 5 : ui32, handshake.name = "br5"} : <i32>
    %64 = br %62 {handshake.bb = 5 : ui32, handshake.name = "br6"} : <i32>
    %65 = br %result_28 {handshake.bb = 5 : ui32, handshake.name = "br7"} : <>
    %66 = mux %69#0 [%55, %63] {handshake.bb = 6 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %67 = mux %69#1 [%56, %64] {handshake.bb = 6 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %68:2 = fork [2] %67 {handshake.bb = 6 : ui32, handshake.name = "fork15"} : <i32>
    %result_30, %index_31 = control_merge [%57, %65]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>, <>] to <>, <i1>
    %69:2 = fork [2] %index_31 {handshake.bb = 6 : ui32, handshake.name = "fork16"} : <i1>
    %70 = source {handshake.bb = 6 : ui32, handshake.name = "source8"} : <>
    %71 = constant %70 {handshake.bb = 6 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %72:2 = fork [2] %71 {handshake.bb = 6 : ui32, handshake.name = "fork17"} : <i32>
    %73 = addi %66, %72#1 {handshake.bb = 6 : ui32, handshake.name = "addi2"} : <i32>
    %74 = cmpi sgt, %68#1, %72#0 {handshake.bb = 6 : ui32, handshake.name = "cmpi4"} : <i32>
    %75:3 = fork [3] %74 {handshake.bb = 6 : ui32, handshake.name = "fork18"} : <i1>
    %trueResult_32, %falseResult_33 = cond_br %75#2, %68#0 {handshake.bb = 6 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    sink %falseResult_33 {handshake.name = "sink3"} : <i32>
    %trueResult_34, %falseResult_35 = cond_br %75#1, %73 {handshake.bb = 6 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    %trueResult_36, %falseResult_37 = cond_br %75#0, %result_30 {handshake.bb = 6 : ui32, handshake.name = "cond_br19"} : <i1>, <>
    %76 = mux %index_39 [%7, %falseResult_35] {handshake.bb = 7 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %result_38, %index_39 = control_merge [%falseResult_3, %falseResult_37]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>, <>] to <>, <i1>
    sink %result_38 {handshake.name = "sink4"} : <>
    end {handshake.bb = 7 : ui32, handshake.name = "end0"} %76, %0#1 : <i32>, <>
  }
}

