module {
  handshake.func @brhash(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["x", "n", "start"], resNames = ["out0", "end"]} {
    %0:4 = fork [4] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = cmpi sgt, %1#1, %2 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %4:4 = fork [4] %3 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %5 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %4#0, %5 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i1>
    sink %falseResult {handshake.name = "sink0"} : <i1>
    %6 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i1> to <i32>
    %trueResult_0, %falseResult_1 = cond_br %4#3, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %4#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %falseResult_3 {handshake.name = "sink1"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %4#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %7 = mux %13#0 [%6, %trueResult_20] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %8 = mux %13#1 [%trueResult_0, %trueResult_22] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %9:2 = fork [2] %8 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %10 = trunci %9#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i1>
    %11 = constant %14 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = true} : <>, <i1>
    %12 = mux %13#2 [%trueResult_2, %trueResult_24] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_4, %trueResult_26]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %13:3 = fork [3] %index {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %14 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %15 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %16 = andi %10, %11 {handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i1>
    %17 = constant %15 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %18 = cmpi eq, %16, %17 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i1>
    %19:4 = fork [4] %18 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i1>
    %trueResult_6, %falseResult_7 = cond_br %19#0, %12 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %19#1, %7 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %19#2, %9#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %19#3, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %20 = merge %falseResult_7 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %21 = merge %falseResult_9 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %22:2 = fork [2] %21 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i32>
    %23 = merge %falseResult_11 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %result_14, %index_15 = control_merge [%falseResult_13]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_15 {handshake.name = "sink2"} : <i1>
    %24 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %25 = constant %24 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 13 : i32} : <>, <i32>
    %26 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %27 = constant %26 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = -306674912 : i32} : <>, <i32>
    %28 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %29 = constant %28 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = 1 : i32} : <>, <i32>
    %30 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %31 = constant %30 {handshake.bb = 2 : ui32, handshake.name = "constant15", value = 4 : i32} : <>, <i32>
    %32 = shrui %23, %29 {handshake.bb = 2 : ui32, handshake.name = "shrui0"} : <i32>
    %33 = xori %32, %27 {handshake.bb = 2 : ui32, handshake.name = "xori0"} : <i32>
    %34:2 = fork [2] %33 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i32>
    %35 = shli %34#1, %31 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i32>
    %36 = addi %34#0, %35 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i32>
    %37 = addi %36, %22#1 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %38:2 = fork [2] %37 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i32>
    %39 = shrui %38#1, %25 {handshake.bb = 2 : ui32, handshake.name = "shrui1"} : <i32>
    %40 = xori %38#0, %39 {handshake.bb = 2 : ui32, handshake.name = "xori1"} : <i32>
    %41 = br %40 {handshake.bb = 2 : ui32, handshake.name = "br2"} : <i32>
    %42 = br %20 {handshake.bb = 2 : ui32, handshake.name = "br3"} : <i32>
    %43 = br %22#0 {handshake.bb = 2 : ui32, handshake.name = "br4"} : <i32>
    %44 = br %result_14 {handshake.bb = 2 : ui32, handshake.name = "br5"} : <>
    %45 = merge %trueResult_6 {handshake.bb = 3 : ui32, handshake.name = "merge3"} : <i32>
    %46 = merge %trueResult_8 {handshake.bb = 3 : ui32, handshake.name = "merge4"} : <i32>
    %47:2 = fork [2] %46 {handshake.bb = 3 : ui32, handshake.name = "fork9"} : <i32>
    %48 = merge %trueResult_10 {handshake.bb = 3 : ui32, handshake.name = "merge5"} : <i32>
    %49:2 = fork [2] %48 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i32>
    %result_16, %index_17 = control_merge [%trueResult_12]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_17 {handshake.name = "sink3"} : <i1>
    %50 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %51 = constant %50 {handshake.bb = 3 : ui32, handshake.name = "constant16", value = 625341585 : i32} : <>, <i32>
    %52 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %53 = constant %52 {handshake.bb = 3 : ui32, handshake.name = "constant17", value = 5 : i32} : <>, <i32>
    %54 = source {handshake.bb = 3 : ui32, handshake.name = "source8"} : <>
    %55 = constant %54 {handshake.bb = 3 : ui32, handshake.name = "constant18", value = 2 : i32} : <>, <i32>
    %56 = source {handshake.bb = 3 : ui32, handshake.name = "source9"} : <>
    %57 = constant %56 {handshake.bb = 3 : ui32, handshake.name = "constant19", value = 9 : i32} : <>, <i32>
    %58 = source {handshake.bb = 3 : ui32, handshake.name = "source10"} : <>
    %59 = constant %58 {handshake.bb = 3 : ui32, handshake.name = "constant20", value = 1 : i32} : <>, <i32>
    %60 = shli %49#1, %57 {handshake.bb = 3 : ui32, handshake.name = "shli0"} : <i32>
    %61 = xori %49#0, %60 {handshake.bb = 3 : ui32, handshake.name = "xori2"} : <i32>
    %62 = shrui %61, %55 {handshake.bb = 3 : ui32, handshake.name = "shrui2"} : <i32>
    %63 = shli %47#1, %59 {handshake.bb = 3 : ui32, handshake.name = "shli1"} : <i32>
    %64 = addi %62, %63 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i32>
    %65:2 = fork [2] %64 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i32>
    %66 = shli %65#1, %53 {handshake.bb = 3 : ui32, handshake.name = "shli2"} : <i32>
    %67 = xori %65#0, %66 {handshake.bb = 3 : ui32, handshake.name = "xori3"} : <i32>
    %68 = xori %67, %51 {handshake.bb = 3 : ui32, handshake.name = "xori4"} : <i32>
    %69 = br %68 {handshake.bb = 3 : ui32, handshake.name = "br6"} : <i32>
    %70 = br %45 {handshake.bb = 3 : ui32, handshake.name = "br7"} : <i32>
    %71 = br %47#0 {handshake.bb = 3 : ui32, handshake.name = "br8"} : <i32>
    %72 = br %result_16 {handshake.bb = 3 : ui32, handshake.name = "br9"} : <>
    %73 = mux %77#0 [%41, %69] {handshake.bb = 4 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %74 = mux %77#1 [%42, %70] {handshake.bb = 4 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %75:2 = fork [2] %74 {handshake.bb = 4 : ui32, handshake.name = "fork12"} : <i32>
    %76 = mux %77#2 [%43, %71] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %result_18, %index_19 = control_merge [%44, %72]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %77:3 = fork [3] %index_19 {handshake.bb = 4 : ui32, handshake.name = "fork13"} : <i1>
    %78 = source {handshake.bb = 4 : ui32, handshake.name = "source11"} : <>
    %79 = constant %78 {handshake.bb = 4 : ui32, handshake.name = "constant21", value = 1 : i32} : <>, <i32>
    %80 = addi %76, %79 {handshake.bb = 4 : ui32, handshake.name = "addi2"} : <i32>
    %81:2 = fork [2] %80 {handshake.bb = 4 : ui32, handshake.name = "fork14"} : <i32>
    %82 = cmpi ne, %81#1, %75#1 {handshake.bb = 4 : ui32, handshake.name = "cmpi2"} : <i32>
    %83:4 = fork [4] %82 {handshake.bb = 4 : ui32, handshake.name = "fork15"} : <i1>
    %trueResult_20, %falseResult_21 = cond_br %83#3, %81#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    sink %falseResult_21 {handshake.name = "sink4"} : <i32>
    %trueResult_22, %falseResult_23 = cond_br %83#2, %73 {handshake.bb = 4 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %83#1, %75#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    sink %falseResult_25 {handshake.name = "sink5"} : <i32>
    %trueResult_26, %falseResult_27 = cond_br %83#0, %result_18 {handshake.bb = 4 : ui32, handshake.name = "cond_br14"} : <i1>, <>
    %84 = mux %index_29 [%falseResult_1, %falseResult_23] {handshake.bb = 5 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %result_28, %index_29 = control_merge [%falseResult_5, %falseResult_27]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    sink %result_28 {handshake.name = "sink6"} : <>
    end {handshake.bb = 5 : ui32, handshake.name = "end0"} %84, %0#1 : <i32>, <>
  }
}

