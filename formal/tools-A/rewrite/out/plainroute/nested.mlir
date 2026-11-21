module {
  handshake.func @nested(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["a", "b", "start"], resNames = ["out0", "end"]} {
    %0:5 = fork [5] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg0 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2 = constant %0#4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = cmpi sgt, %1#1, %2 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %4:5 = fork [5] %3 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %5 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %4#0, %5 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i1>
    sink %falseResult {handshake.name = "sink0"} : <i1>
    %6 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i1> to <i32>
    %7 = constant %0#1 {handshake.bb = 0 : ui32, handshake.name = "constant7", value = true} : <>, <i1>
    %trueResult_0, %falseResult_1 = cond_br %4#1, %7 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i1>
    %8 = extui %falseResult_1 {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i1> to <i32>
    %9 = extui %trueResult_0 {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i1> to <i32>
    %rr0s = source {handshake.bb = 0 : ui32, handshake.name = "sourcerr0"} : <>
    %rr0c = constant %rr0s {handshake.bb = 0 : ui32, handshake.name = "constantrr0", value = -1 : i32} : <>, <i32>
    %rr0d = addi %1#0, %rr0c {handshake.bb = 0 : ui32, handshake.name = "addirr0"} : <i32>
    %trueResult_2, %falseResult_3 = cond_br %4#4, %rr0d {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    sink %falseResult_3 {handshake.name = "sink1"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %4#3, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_5 {handshake.name = "sink2"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %4#2, %0#3 {handshake.bb = 0 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %10 = mux %15#0 [%6, %trueResult_36] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %11 = mux %15#1 [%9, %trueResult_38] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %12 = mux %15#2 [%trueResult_2, %trueResult_40] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %13 = mux %15#3 [%trueResult_4, %trueResult_42] {handshake.bb = 1 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %14:2 = fork [2] %13 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %result, %index = control_merge [%trueResult_6, %trueResult_44]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %15:4 = fork [4] %index {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %16:3 = fork [3] %result {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <>
    %17 = constant %16#2 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 0 : i32} : <>, <i32>
    %18 = cmpi sgt, %14#1, %17 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %19:6 = fork [6] %18 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i1>
    %20 = constant %16#0 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = false} : <>, <i1>
    %trueResult_8, %falseResult_9 = cond_br %19#0, %20 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i1>
    sink %falseResult_9 {handshake.name = "sink3"} : <i1>
    %21 = extui %trueResult_8 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i1> to <i32>
    %trueResult_10, %falseResult_11 = cond_br %19#5, %11 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %19#4, %12 {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %19#3, %14#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %19#2, %10 {handshake.bb = 1 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %19#1, %16#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br14"} : <i1>, <>
    %22 = mux %31#0 [%21, %trueResult_22] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %23:2 = fork [2] %22 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i32>
    %24 = mux %31#1 [%trueResult_10, %trueResult_24] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %25:2 = fork [2] %24 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i32>
    %26 = mux %31#2 [%trueResult_12, %trueResult_26] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %27 = mux %31#3 [%trueResult_14, %trueResult_28] {handshake.bb = 2 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %28:2 = fork [2] %27 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i32>
    %29 = mux %31#4 [%trueResult_16, %trueResult_30] {handshake.bb = 2 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %30:2 = fork [2] %29 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <i32>
    %result_20, %index_21 = control_merge [%trueResult_18, %trueResult_32]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %31:5 = fork [5] %index_21 {handshake.bb = 2 : ui32, handshake.name = "fork11"} : <i1>
    %32 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %33 = constant %32 {handshake.bb = 2 : ui32, handshake.name = "constant4", value = 3 : i32} : <>, <i32>
    %34 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %35 = constant %34 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %36 = shli %25#1, %33 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i32>
    %37 = xori %25#0, %36 {handshake.bb = 2 : ui32, handshake.name = "xori0"} : <i32>
    %38 = addi %37, %30#1 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %39 = addi %38, %23#1 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %40 = addi %23#0, %35 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %41:2 = fork [2] %40 {handshake.bb = 2 : ui32, handshake.name = "fork12"} : <i32>
    %42 = cmpi slt, %41#1, %28#1 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i32>
    %43:6 = fork [6] %42 {handshake.bb = 2 : ui32, handshake.name = "fork13"} : <i1>
    %trueResult_22, %falseResult_23 = cond_br %43#5, %41#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    sink %falseResult_23 {handshake.name = "sink4"} : <i32>
    %trueResult_24, %falseResult_25 = cond_br %43#4, %39 {handshake.bb = 2 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_26, %falseResult_27 = cond_br %43#3, %26 {handshake.bb = 2 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_28, %falseResult_29 = cond_br %43#2, %28#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    %trueResult_30, %falseResult_31 = cond_br %43#1, %30#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br19"} : <i1>, <i32>
    %trueResult_32, %falseResult_33 = cond_br %43#0, %result_20 {handshake.bb = 2 : ui32, handshake.name = "cond_br20"} : <i1>, <>
    %44 = mux %49#0 [%falseResult_11, %falseResult_25] {handshake.bb = 3 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %45 = mux %49#1 [%falseResult_13, %falseResult_27] {handshake.bb = 3 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %46:2 = fork [2] %45 {handshake.bb = 3 : ui32, handshake.name = "fork14"} : <i32>
    %47 = mux %49#2 [%falseResult_15, %falseResult_29] {handshake.bb = 3 : ui32, handshake.name = "mux11"} : <i1>, [<i32>, <i32>] to <i32>
    %48 = mux %49#3 [%falseResult_17, %falseResult_31] {handshake.bb = 3 : ui32, handshake.name = "mux12"} : <i1>, [<i32>, <i32>] to <i32>
    %result_34, %index_35 = control_merge [%falseResult_19, %falseResult_33]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %49:4 = fork [4] %index_35 {handshake.bb = 3 : ui32, handshake.name = "fork15"} : <i1>
    %50 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %51 = constant %50 {handshake.bb = 3 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %rrf:2 = fork [2] %48 {handshake.bb = 3 : ui32, handshake.name = "forkrrf"} : <i32>
    %52 = addi %rrf#0, %51 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i32>
    %54 = cmpi slt, %rrf#1, %46#1 {handshake.bb = 3 : ui32, handshake.name = "cmpi3"} : <i32>
    %55:5 = fork [5] %54 {handshake.bb = 3 : ui32, handshake.name = "fork17"} : <i1>
    %trueResult_36, %falseResult_37 = cond_br %55#4, %52 {handshake.bb = 3 : ui32, handshake.name = "cond_br21"} : <i1>, <i32>
    sink %falseResult_37 {handshake.name = "sink5"} : <i32>
    %trueResult_38, %falseResult_39 = cond_br %55#3, %44 {handshake.bb = 3 : ui32, handshake.name = "cond_br22"} : <i1>, <i32>
    %trueResult_40, %falseResult_41 = cond_br %55#2, %46#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br23"} : <i1>, <i32>
    sink %falseResult_41 {handshake.name = "sink6"} : <i32>
    %trueResult_42, %falseResult_43 = cond_br %55#1, %47 {handshake.bb = 3 : ui32, handshake.name = "cond_br24"} : <i1>, <i32>
    sink %falseResult_43 {handshake.name = "sink7"} : <i32>
    %trueResult_44, %falseResult_45 = cond_br %55#0, %result_34 {handshake.bb = 3 : ui32, handshake.name = "cond_br25"} : <i1>, <>
    %56 = mux %index_47 [%8, %falseResult_39] {handshake.bb = 4 : ui32, handshake.name = "mux13"} : <i1>, [<i32>, <i32>] to <i32>
    %result_46, %index_47 = control_merge [%falseResult_7, %falseResult_45]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    sink %result_46 {handshake.name = "sink8"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %56, %0#2 : <i32>, <>
  }
}

