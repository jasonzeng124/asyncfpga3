module {
  handshake.func @iterative_division(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["dividend", "divisor", "start"], resNames = ["out0", "end"]} {
    %0:3 = fork [3] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %3 = constant %2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %4 = cmpi eq, %1#1, %3 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %5:4 = fork [4] %4 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %6 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = true} : <>, <i1>
    %trueResult, %falseResult = cond_br %5#0, %6 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i1>
    sink %falseResult {handshake.name = "sink0"} : <i1>
    %7 = extsi %trueResult {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i1> to <i32>
    %trueResult_0, %falseResult_1 = cond_br %5#3, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %5#2, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %trueResult_2 {handshake.name = "sink1"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %5#1, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    sink %trueResult_4 {handshake.name = "sink2"} : <i32>
    %8 = merge %falseResult_3 {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %9:4 = fork [4] %8 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %10 = merge %falseResult_5 {handshake.bb = 1 : ui32, handshake.name = "merge1"} : <i32>
    %11:4 = fork [4] %10 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %result, %index = control_merge [%falseResult_1]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    sink %index {handshake.name = "sink3"} : <i1>
    %12:3 = fork [3] %result {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <>
    %13 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %14 = constant %13 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = -1 : i32} : <>, <i32>
    %15:2 = fork [2] %14 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i32>
    %16 = constant %12#2 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 0 : i32} : <>, <i32>
    %17:2 = fork [2] %16 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i32>
    %18 = cmpi sgt, %9#3, %15#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %19 = subi %17#1, %9#2 {handshake.bb = 1 : ui32, handshake.name = "subi0"} : <i32>
    %20 = select %18[%9#1, %19] {handshake.bb = 1 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %21:2 = fork [2] %20 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i32>
    %22 = cmpi sgt, %11#3, %15#0 {handshake.bb = 1 : ui32, handshake.name = "cmpi2"} : <i32>
    %23 = subi %17#0, %11#2 {handshake.bb = 1 : ui32, handshake.name = "subi1"} : <i32>
    %24 = select %22[%11#1, %23] {handshake.bb = 1 : ui32, handshake.name = "select1"} : <i1>, <i32>
    %25:2 = fork [2] %24 {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <i32>
    %26 = cmpi slt, %21#1, %25#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi3"} : <i32>
    %27:6 = fork [6] %26 {handshake.bb = 1 : ui32, handshake.name = "fork10"} : <i1>
    %28 = constant %12#0 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = false} : <>, <i1>
    %trueResult_6, %falseResult_7 = cond_br %27#0, %28 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i1>
    %29 = extui %falseResult_7 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i1> to <i32>
    %30 = extui %trueResult_6 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i1> to <i32>
    %trueResult_8, %falseResult_9 = cond_br %27#5, %9#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %27#4, %11#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %27#3, %12#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %trueResult_14, %falseResult_15 = cond_br %27#2, %21#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    sink %trueResult_14 {handshake.name = "sink4"} : <i32>
    %trueResult_16, %falseResult_17 = cond_br %27#1, %25#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    sink %trueResult_16 {handshake.name = "sink5"} : <i32>
    %31 = mux %37#0 [%falseResult_15, %falseResult_29] {handshake.bb = 2 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %32 = mux %37#1 [%29, %falseResult_21] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %33 = mux %37#2 [%falseResult_9, %falseResult_23] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %34 = mux %37#3 [%falseResult_11, %falseResult_25] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %35 = mux %37#4 [%falseResult_17, %falseResult_31] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %36:3 = fork [3] %35 {handshake.bb = 2 : ui32, handshake.name = "fork11"} : <i32>
    %result_18, %index_19 = control_merge [%falseResult_13, %falseResult_27]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %37:5 = fork [5] %index_19 {handshake.bb = 2 : ui32, handshake.name = "fork12"} : <i1>
    %38 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %39 = constant %38 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %40 = subi %31, %36#2 {handshake.bb = 2 : ui32, handshake.name = "subi2"} : <i32>
    %41:2 = fork [2] %40 {handshake.bb = 2 : ui32, handshake.name = "fork13"} : <i32>
    %42 = addi %32, %39 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %43 = cmpi slt, %41#1, %36#1 {handshake.bb = 2 : ui32, handshake.name = "cmpi4"} : <i32>
    %44:6 = fork [6] %43 {handshake.bb = 2 : ui32, handshake.name = "fork14"} : <i1>
    %trueResult_20, %falseResult_21 = cond_br %44#5, %42 {handshake.bb = 2 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %44#4, %33 {handshake.bb = 2 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %44#3, %34 {handshake.bb = 2 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %trueResult_26, %falseResult_27 = cond_br %44#2, %result_18 {handshake.bb = 2 : ui32, handshake.name = "cond_br16"} : <i1>, <>
    %trueResult_28, %falseResult_29 = cond_br %44#1, %41#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    sink %trueResult_28 {handshake.name = "sink6"} : <i32>
    %trueResult_30, %falseResult_31 = cond_br %44#0, %36#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    sink %trueResult_30 {handshake.name = "sink7"} : <i32>
    %45 = mux %49#0 [%30, %trueResult_20] {handshake.bb = 3 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %46:2 = fork [2] %45 {handshake.bb = 3 : ui32, handshake.name = "fork15"} : <i32>
    %47 = mux %49#1 [%trueResult_8, %trueResult_22] {handshake.bb = 3 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %48 = mux %49#2 [%trueResult_10, %trueResult_24] {handshake.bb = 3 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %result_32, %index_33 = control_merge [%trueResult_12, %trueResult_26]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %49:3 = fork [3] %index_33 {handshake.bb = 3 : ui32, handshake.name = "fork16"} : <i1>
    %50 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %51 = constant %50 {handshake.bb = 3 : ui32, handshake.name = "constant6", value = 0 : i32} : <>, <i32>
    %52:2 = fork [2] %51 {handshake.bb = 3 : ui32, handshake.name = "fork17"} : <i32>
    %53 = xori %47, %48 {handshake.bb = 3 : ui32, handshake.name = "xori0"} : <i32>
    %54 = cmpi slt, %53, %52#1 {handshake.bb = 3 : ui32, handshake.name = "cmpi5"} : <i32>
    %55 = subi %52#0, %46#1 {handshake.bb = 3 : ui32, handshake.name = "subi3"} : <i32>
    %56 = select %54[%55, %46#0] {handshake.bb = 3 : ui32, handshake.name = "select2"} : <i1>, <i32>
    %57 = br %56 {handshake.bb = 3 : ui32, handshake.name = "br1"} : <i32>
    %58 = br %result_32 {handshake.bb = 3 : ui32, handshake.name = "br2"} : <>
    %59 = mux %index_35 [%7, %57] {handshake.bb = 4 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %result_34, %index_35 = control_merge [%trueResult_0, %58]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    sink %result_34 {handshake.name = "sink8"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %59, %0#1 : <i32>, <>
  }
}

