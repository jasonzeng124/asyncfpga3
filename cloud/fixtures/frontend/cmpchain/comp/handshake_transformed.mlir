module {
  handshake.func @cmpchain(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["x", "y", "start"], resNames = ["out0", "end"]} {
    %0:3 = fork [3] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2:2 = fork [2] %arg0 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i32>
    %3 = cmpi eq, %2#1, %1#1 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %4:4 = fork [4] %3 {handshake.bb = 0 : ui32, handshake.name = "fork3"} : <i1>
    %5 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = -268435456 : i29} : <>, <i29>
    %trueResult, %falseResult = cond_br %4#0, %5 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i29>
    sink %falseResult {handshake.name = "sink0"} : <i29>
    %6 = extui %trueResult {handshake.bb = 5 : ui32, handshake.name = "extui0"} : <i29> to <i31>
    %trueResult_0, %falseResult_1 = cond_br %4#3, %2#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %4#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %4#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %7 = merge %falseResult_1 {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %8:2 = fork [2] %7 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %9 = merge %falseResult_3 {handshake.bb = 1 : ui32, handshake.name = "merge1"} : <i32>
    %10:2 = fork [2] %9 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %result, %index = control_merge [%falseResult_5]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    sink %index {handshake.name = "sink1"} : <i1>
    %11:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %13 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant11", value = -1 : i32} : <>, <i32>
    %14 = andi %8#1, %10#1 {handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i32>
    %15 = cmpi sgt, %14, %13 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %16:4 = fork [4] %15 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i1>
    %trueResult_6, %falseResult_7 = cond_br %16#3, %8#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %16#2, %10#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %16#1, %11#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %17 = constant %11#0 {handshake.bb = 1 : ui32, handshake.name = "constant1", value = -536870912 : i30} : <>, <i30>
    %trueResult_12, %falseResult_13 = cond_br %16#0, %17 {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <i30>
    sink %trueResult_12 {handshake.name = "sink2"} : <i30>
    %18 = extui %falseResult_13 {handshake.bb = 5 : ui32, handshake.name = "extui1"} : <i30> to <i31>
    %19 = merge %trueResult_6 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %20:2 = fork [2] %19 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i32>
    %21 = merge %trueResult_8 {handshake.bb = 2 : ui32, handshake.name = "merge3"} : <i32>
    %22:2 = fork [2] %21 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i32>
    %result_14, %index_15 = control_merge [%trueResult_10]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_15 {handshake.name = "sink3"} : <i1>
    %23:2 = fork [2] %result_14 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <>
    %24 = cmpi slt, %20#1, %22#1 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i32>
    %25:4 = fork [4] %24 {handshake.bb = 2 : ui32, handshake.name = "fork11"} : <i1>
    %26 = constant %23#0 {handshake.bb = 2 : ui32, handshake.name = "constant2", value = -268435456 : i29} : <>, <i29>
    %trueResult_16, %falseResult_17 = cond_br %25#0, %26 {handshake.bb = 2 : ui32, handshake.name = "cond_br12"} : <i1>, <i29>
    sink %falseResult_17 {handshake.name = "sink4"} : <i29>
    %27 = extsi %trueResult_16 {handshake.bb = 2 : ui32, handshake.name = "extsi0"} : <i29> to <i30>
    %28 = extui %27 {handshake.bb = 5 : ui32, handshake.name = "extui2"} : <i30> to <i31>
    %trueResult_18, %falseResult_19 = cond_br %25#3, %20#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %25#2, %22#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %25#1, %23#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %29 = merge %falseResult_19 {handshake.bb = 3 : ui32, handshake.name = "merge4"} : <i32>
    %30:2 = fork [2] %29 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <i32>
    %31 = merge %falseResult_21 {handshake.bb = 3 : ui32, handshake.name = "merge5"} : <i32>
    %32:2 = fork [2] %31 {handshake.bb = 3 : ui32, handshake.name = "fork13"} : <i32>
    %result_24, %index_25 = control_merge [%falseResult_23]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_25 {handshake.name = "sink5"} : <i1>
    %33:2 = fork [2] %result_24 {handshake.bb = 3 : ui32, handshake.name = "fork14"} : <>
    %34 = cmpi ugt, %30#1, %32#1 {handshake.bb = 3 : ui32, handshake.name = "cmpi3"} : <i32>
    %35:4 = fork [4] %34 {handshake.bb = 3 : ui32, handshake.name = "fork15"} : <i1>
    %36 = constant %33#0 {handshake.bb = 3 : ui32, handshake.name = "constant3", value = -1073741824 : i31} : <>, <i31>
    %trueResult_26, %falseResult_27 = cond_br %35#0, %36 {handshake.bb = 3 : ui32, handshake.name = "cond_br16"} : <i1>, <i31>
    sink %falseResult_27 {handshake.name = "sink6"} : <i31>
    %trueResult_28, %falseResult_29 = cond_br %35#3, %30#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_30, %falseResult_31 = cond_br %35#2, %32#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    %trueResult_32, %falseResult_33 = cond_br %35#1, %33#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br19"} : <i1>, <>
    %37 = merge %falseResult_29 {handshake.bb = 4 : ui32, handshake.name = "merge6"} : <i32>
    %38:3 = fork [3] %37 {handshake.bb = 4 : ui32, handshake.name = "fork16"} : <i32>
    %39 = merge %falseResult_31 {handshake.bb = 4 : ui32, handshake.name = "merge7"} : <i32>
    %result_34, %index_35 = control_merge [%falseResult_33]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_35 {handshake.name = "sink7"} : <i1>
    %40 = source {handshake.bb = 4 : ui32, handshake.name = "source1"} : <>
    %41 = source {handshake.bb = 4 : ui32, handshake.name = "source2"} : <>
    %42 = source {handshake.bb = 4 : ui32, handshake.name = "source3"} : <>
    %43 = source {handshake.bb = 4 : ui32, handshake.name = "source4"} : <>
    %44 = constant %43 {handshake.bb = 4 : ui32, handshake.name = "constant17", value = 256 : i32} : <>, <i32>
    %45 = source {handshake.bb = 4 : ui32, handshake.name = "source5"} : <>
    %46 = constant %45 {handshake.bb = 4 : ui32, handshake.name = "constant18", value = 999999 : i32} : <>, <i32>
    %47 = cmpi sgt, %38#2, %46 {handshake.bb = 4 : ui32, handshake.name = "cmpi4"} : <i32>
    %48 = cmpi ult, %38#1, %44 {handshake.bb = 4 : ui32, handshake.name = "cmpi5"} : <i32>
    %49 = constant %42 {handshake.bb = 4 : ui32, handshake.name = "constant4", value = -536870912 : i30} : <>, <i30>
    %50 = constant %41 {handshake.bb = 4 : ui32, handshake.name = "constant5", value = -268435456 : i30} : <>, <i30>
    %51 = select %48[%49, %50] {handshake.bb = 4 : ui32, handshake.name = "select0"} : <i1>, <i30>
    %52 = extsi %51 {handshake.bb = 4 : ui32, handshake.name = "extsi1"} : <i30> to <i31>
    %53 = constant %40 {handshake.bb = 4 : ui32, handshake.name = "constant7", value = -805306368 : i31} : <>, <i31>
    %54 = select %47[%53, %52] {handshake.bb = 4 : ui32, handshake.name = "select1"} : <i1>, <i31>
    %55 = br %54 {handshake.bb = 4 : ui32, handshake.name = "br1"} : <i31>
    %56 = br %38#0 {handshake.bb = 4 : ui32, handshake.name = "br2"} : <i32>
    %57 = br %39 {handshake.bb = 4 : ui32, handshake.name = "br3"} : <i32>
    %58 = br %result_34 {handshake.bb = 4 : ui32, handshake.name = "br4"} : <>
    %59 = mux %63#0 [%6, %18, %28, %trueResult_26, %55] {handshake.bb = 5 : ui32, handshake.name = "mux0"} : <i3>, [<i31>, <i31>, <i31>, <i31>, <i31>] to <i31>
    %60 = extui %59 {handshake.bb = 5 : ui32, handshake.name = "extui3"} : <i31> to <i32>
    %61 = mux %63#1 [%trueResult_0, %falseResult_7, %trueResult_18, %trueResult_28, %56] {handshake.bb = 5 : ui32, handshake.name = "mux1"} : <i3>, [<i32>, <i32>, <i32>, <i32>, <i32>] to <i32>
    %62 = mux %63#2 [%trueResult_2, %falseResult_9, %trueResult_20, %trueResult_30, %57] {handshake.bb = 5 : ui32, handshake.name = "mux2"} : <i3>, [<i32>, <i32>, <i32>, <i32>, <i32>] to <i32>
    %result_36, %index_37 = control_merge [%trueResult_4, %falseResult_11, %trueResult_22, %trueResult_32, %58]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>, <>, <>, <>] to <>, <i3>
    %63:3 = fork [3] %index_37 {handshake.bb = 5 : ui32, handshake.name = "fork17"} : <i3>
    sink %result_36 {handshake.name = "sink8"} : <>
    %64 = subi %61, %62 {handshake.bb = 5 : ui32, handshake.name = "subi0"} : <i32>
    %65 = xori %60, %64 {handshake.bb = 5 : ui32, handshake.name = "xori0"} : <i32>
    end {handshake.bb = 5 : ui32, handshake.name = "end0"} %65, %0#1 : <i32>, <>
  }
}

