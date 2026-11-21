module {
  handshake.func @twoloops(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["a", "n", "start"], resNames = ["out0", "end"]} {
    %0:4 = fork [4] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = cmpi sgt, %1#1, %2 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %4:4 = fork [4] %3 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %trueResult, %falseResult = cond_br %4#3, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %5 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %trueResult_0, %falseResult_1 = cond_br %4#0, %5 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i1>
    sink %falseResult_1 {handshake.name = "sink0"} : <i1>
    %6 = extui %trueResult_0 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i1> to <i32>
    %rr0s = source {handshake.bb = 0 : ui32, handshake.name = "sourcerr0"} : <>
    %rr0c = constant %rr0s {handshake.bb = 0 : ui32, handshake.name = "constantrr0", value = -1 : i32} : <>, <i32>
    %rr0d = addi %1#0, %rr0c {handshake.bb = 0 : ui32, handshake.name = "addirr0"} : <i32>
    %trueResult_2, %falseResult_3 = cond_br %4#2, %rr0d {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    sink %falseResult_3 {handshake.name = "sink1"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %4#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %7 = mux %13#0 [%trueResult, %trueResult_6] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %8:2 = fork [2] %7 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %9 = mux %13#1 [%6, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %10:2 = fork [2] %9 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %11 = mux %13#2 [%trueResult_2, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %12:2 = fork [2] %11 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %result, %index = control_merge [%trueResult_4, %trueResult_12]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %13:3 = fork [3] %index {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i1>
    %14 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %15 = constant %14 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %16 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %17 = constant %16 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 7 : i32} : <>, <i32>
    %18 = shli %8#1, %17 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %19 = xori %8#0, %18 {handshake.bb = 1 : ui32, handshake.name = "xori0"} : <i32>
    %20 = addi %19, %10#1 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %rrf:2 = fork [2] %10#0 {handshake.bb = 1 : ui32, handshake.name = "forkrrf"} : <i32>
    %21 = addi %rrf#0, %15 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %23 = cmpi slt, %rrf#1, %12#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %24:4 = fork [4] %23 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i1>
    %trueResult_6, %falseResult_7 = cond_br %24#3, %20 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %24#2, %21 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    sink %falseResult_9 {handshake.name = "sink2"} : <i32>
    %trueResult_10, %falseResult_11 = cond_br %24#1, %12#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    sink %falseResult_11 {handshake.name = "sink3"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %24#0, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %25 = mux %index_15 [%falseResult, %falseResult_7] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %26:2 = fork [2] %25 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i32>
    %27 = trunci %26#0 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i32> to <i8>
    %28 = constant %30 {handshake.bb = 2 : ui32, handshake.name = "constant2", value = -1 : i8} : <>, <i8>
    %result_14, %index_15 = control_merge [%falseResult_5, %falseResult_13]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %29:3 = fork [3] %result_14 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <>
    %30 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %31 = andi %27, %28 {handshake.bb = 2 : ui32, handshake.name = "andi0"} : <i8>
    %32:2 = fork [2] %31 {handshake.bb = 2 : ui32, handshake.name = "fork11"} : <i8>
    %33 = constant %29#0 {handshake.bb = 2 : ui32, handshake.name = "constant3", value = 0 : i8} : <>, <i8>
    %34 = cmpi ugt, %32#1, %33 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i8>
    %35:4 = fork [4] %34 {handshake.bb = 2 : ui32, handshake.name = "fork12"} : <i1>
    %36 = constant %29#1 {handshake.bb = 2 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %trueResult_16, %falseResult_17 = cond_br %35#3, %36 {handshake.bb = 2 : ui32, handshake.name = "cond_br12"} : <i1>, <i1>
    sink %falseResult_17 {handshake.name = "sink4"} : <i1>
    %37 = extui %trueResult_16 {handshake.bb = 2 : ui32, handshake.name = "extui1"} : <i1> to <i8>
    %trueResult_18, %falseResult_19 = cond_br %35#1, %26#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %35#0, %32#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br14"} : <i1>, <i8>
    sink %falseResult_21 {handshake.name = "sink5"} : <i8>
    %trueResult_22, %falseResult_23 = cond_br %35#2, %29#2 {handshake.bb = 2 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %38 = mux %46#0 [%37, %trueResult_26] {handshake.bb = 3 : ui32, handshake.name = "mux4"} : <i1>, [<i8>, <i8>] to <i8>
    %39 = extui %38 {handshake.bb = 3 : ui32, handshake.name = "extui2"} : <i8> to <i9>
    %40 = constant %51 {handshake.bb = 3 : ui32, handshake.name = "constant5", value = 1 : i9} : <>, <i9>
    %41 = mux %46#2 [%trueResult_18, %trueResult_28] {handshake.bb = 3 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %42:2 = fork [2] %41 {handshake.bb = 3 : ui32, handshake.name = "fork13"} : <i32>
    %43 = mux %46#1 [%trueResult_20, %trueResult_30] {handshake.bb = 3 : ui32, handshake.name = "mux6"} : <i1>, [<i8>, <i8>] to <i8>
    %44:2 = fork [2] %43 {handshake.bb = 3 : ui32, handshake.name = "fork14"} : <i8>
    %45 = extui %44#0 {handshake.bb = 3 : ui32, handshake.name = "extui3"} : <i8> to <i9>
    %result_24, %index_25 = control_merge [%trueResult_22, %trueResult_32]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %46:3 = fork [3] %index_25 {handshake.bb = 3 : ui32, handshake.name = "fork15"} : <i1>
    %47 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %48 = constant %47 {handshake.bb = 3 : ui32, handshake.name = "constant10", value = 40503 : i32} : <>, <i32>
    %49 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %50 = constant %49 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = 3 : i32} : <>, <i32>
    %51 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %52 = shrui %42#1, %50 {handshake.bb = 3 : ui32, handshake.name = "shrui0"} : <i32>
    %53 = xori %42#0, %52 {handshake.bb = 3 : ui32, handshake.name = "xori1"} : <i32>
    %54 = addi %53, %48 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i32>
    %55 = addi %39, %40 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i9>
    %56:2 = fork [2] %55 {handshake.bb = 3 : ui32, handshake.name = "fork16"} : <i9>
    %57 = trunci %56#0 {handshake.bb = 3 : ui32, handshake.name = "trunci1"} : <i9> to <i8>
    %58 = cmpi ult, %56#1, %45 {handshake.bb = 3 : ui32, handshake.name = "cmpi3"} : <i9>
    %59:4 = fork [4] %58 {handshake.bb = 3 : ui32, handshake.name = "fork17"} : <i1>
    %trueResult_26, %falseResult_27 = cond_br %59#0, %57 {handshake.bb = 3 : ui32, handshake.name = "cond_br16"} : <i1>, <i8>
    sink %falseResult_27 {handshake.name = "sink6"} : <i8>
    %trueResult_28, %falseResult_29 = cond_br %59#1, %54 {handshake.bb = 3 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_30, %falseResult_31 = cond_br %59#3, %44#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br18"} : <i1>, <i8>
    sink %falseResult_31 {handshake.name = "sink7"} : <i8>
    %trueResult_32, %falseResult_33 = cond_br %59#2, %result_24 {handshake.bb = 3 : ui32, handshake.name = "cond_br19"} : <i1>, <>
    %60 = mux %index_35 [%falseResult_19, %falseResult_29] {handshake.bb = 4 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %result_34, %index_35 = control_merge [%falseResult_23, %falseResult_33]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    sink %result_34 {handshake.name = "sink8"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %60, %0#1 : <i32>, <>
  }
}

