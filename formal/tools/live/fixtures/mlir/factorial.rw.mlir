module {
  handshake.func @factorial(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["n", "start"], resNames = ["out0", "end"]} {
    %0:3 = fork [3] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg0 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %3 = constant %2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 2 : i32} : <>, <i32>
    %4 = cmpi sgt, %1#1, %3 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %5:3 = fork [3] %4 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %trueResult, %falseResult = cond_br %5#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %6 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = true} : <>, <i1>
    %trueResult_0, %falseResult_1 = cond_br %5#0, %6 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i1>
    %7 = extui %falseResult_1 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i1> to <i32>
    %8 = extui %trueResult_0 {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i1> to <i32>
    %trueResult_2, %falseResult_3 = cond_br %5#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %9 = mux %12#0 [%7, %falseResult_15] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %10 = mux %12#1 [%falseResult, %falseResult_13] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %11:2 = fork [2] %10 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %result, %index = control_merge [%falseResult_3, %falseResult_17]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %12:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %13 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %14 = constant %13 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 0 : i32} : <>, <i32>
    %15 = cmpi sgt, %11#1, %14 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %16:3 = fork [3] %15 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i1>
    %trueResult_4, %falseResult_5 = cond_br %16#2, %11#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_5 {handshake.name = "sink0"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %16#1, %9 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %16#0, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %17 = mux %20#0 [%trueResult, %trueResult_12] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %18:4 = fork [4] %17 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i32>
    %19 = mux %20#1 [%8, %trueResult_14] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_10, %index_11 = control_merge [%trueResult_2, %trueResult_16]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %20:2 = fork [2] %index_11 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i1>
    %21 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %22 = constant %21 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = -3 : i32} : <>, <i32>
    %23 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %24 = constant %23 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = -2 : i32} : <>, <i32>
    %25 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %26 = constant %25 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = -1 : i32} : <>, <i32>
    %27 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %28 = constant %27 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 2 : i32} : <>, <i32>
    %29 = addi %18#3, %26 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %30 = muli %18#2, %29 {handshake.bb = 2 : ui32, handshake.name = "muli0"} : <i32>
    %31 = addi %18#1, %24 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %32 = muli %30, %31 {handshake.bb = 2 : ui32, handshake.name = "muli1"} : <i32>
    %33 = muli %19, %32 {handshake.bb = 2 : ui32, handshake.name = "muli2"} : <i32>
    %34 = addi %18#0, %22 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %35:2 = fork [2] %34 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i32>
    %36 = cmpi sgt, %35#1, %28 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i32>
    %37:3 = fork [3] %36 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult_12, %falseResult_13 = cond_br %37#2, %35#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %37#1, %33 {handshake.bb = 2 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %37#0, %result_10 {handshake.bb = 2 : ui32, handshake.name = "cond_br12"} : <i1>, <>
    %38 = mux %41#0 [%trueResult_4, %trueResult_20] {handshake.bb = 3 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %39:2 = fork [2] %38 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i32>
    %40 = mux %41#1 [%trueResult_6, %trueResult_22] {handshake.bb = 3 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %result_18, %index_19 = control_merge [%trueResult_8, %trueResult_24]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %41:2 = fork [2] %index_19 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i1>
    %42 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %43 = constant %42 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = -1 : i32} : <>, <i32>
    %44 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %45 = constant %44 {handshake.bb = 3 : ui32, handshake.name = "constant12", value = 0 : i32} : <>, <i32>
    %46 = muli %40, %39#1 {handshake.bb = 3 : ui32, handshake.name = "muli3"} : <i32>
    %47 = addi %39#0, %43 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i32>
    %48:2 = fork [2] %47 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <i32>
    %49 = cmpi sgt, %48#1, %45 {handshake.bb = 3 : ui32, handshake.name = "cmpi3"} : <i32>
    %50:3 = fork [3] %49 {handshake.bb = 3 : ui32, handshake.name = "fork13"} : <i1>
    %trueResult_20, %falseResult_21 = cond_br %50#2, %48#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    sink %falseResult_21 {handshake.name = "sink1"} : <i32>
    %trueResult_22, %falseResult_23 = cond_br %50#1, %46 {handshake.bb = 3 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %50#0, %result_18 {handshake.bb = 3 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %51 = mux %index_27 [%falseResult_7, %falseResult_23] {handshake.bb = 4 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %result_26, %index_27 = control_merge [%falseResult_9, %falseResult_25]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    sink %result_26 {handshake.name = "sink2"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %51, %0#1 : <i32>, <>
  }
}

