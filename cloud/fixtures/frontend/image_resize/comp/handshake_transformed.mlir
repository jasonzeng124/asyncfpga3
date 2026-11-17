module {
  handshake.func @image_resize(%arg0: memref<900xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "c", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:3 = fork [3] %arg3 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg0 : memref<900xi32>] %arg2 (%38, %addressResult, %addressResult_2, %dataResult_3) %result_22 {connectedBlocks = [2 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i10>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %3 = extui %2 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i1> to <i5>
    %4 = br %arg1 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %5 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %6 = mux %9#0 [%3, %trueResult_16] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i5>, <i5>] to <i5>
    %7:3 = fork [3] %6 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i5>
    %8 = mux %9#1 [%4, %trueResult_18] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%5, %trueResult_20]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %9:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i1>
    %10:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <>
    %11 = constant %10#0 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %12 = br %11 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i1>
    %13 = extui %12 {handshake.bb = 2 : ui32, handshake.name = "extui5"} : <i1> to <i5>
    %14 = br %8 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i32>
    %15 = br %7#2 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i5>
    %16 = br %7#0 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i5>
    %17 = br %7#1 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <i5>
    %18 = br %10#1 {handshake.bb = 1 : ui32, handshake.name = "br10"} : <>
    %19 = mux %36#3 [%13, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i5>, <i5>] to <i5>
    %20:3 = fork [3] %19 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i5>
    %21 = extui %20#0 {handshake.bb = 2 : ui32, handshake.name = "extui6"} : <i5> to <i10>
    %22 = extui %20#1 {handshake.bb = 2 : ui32, handshake.name = "extui7"} : <i5> to <i10>
    %23 = extui %20#2 {handshake.bb = 2 : ui32, handshake.name = "extui8"} : <i5> to <i6>
    %24 = constant %40 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 1 : i6} : <>, <i6>
    %25 = mux %36#4 [%14, %trueResult_4] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %26:2 = fork [2] %25 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i32>
    %27 = mux %36#2 [%15, %trueResult_6] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i5>, <i5>] to <i5>
    %28 = mux %36#0 [%16, %trueResult_8] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i5>, <i5>] to <i5>
    %29:2 = fork [2] %28 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i5>
    %30 = extui %29#1 {handshake.bb = 2 : ui32, handshake.name = "extui9"} : <i5> to <i64>
    %31:4 = fork [4] %30 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i64>
    %32 = mux %36#1 [%17, %trueResult_10] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<i5>, <i5>] to <i5>
    %33:2 = fork [2] %32 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i5>
    %34 = extui %33#1 {handshake.bb = 2 : ui32, handshake.name = "extui10"} : <i5> to <i64>
    %35:4 = fork [4] %34 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i64>
    %result_0, %index_1 = control_merge [%18, %trueResult_12]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %36:5 = fork [5] %index_1 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <i1>
    %37:2 = fork [2] %result_0 {handshake.bb = 2 : ui32, handshake.name = "fork11"} : <>
    %38 = constant %37#0 {handshake.bb = 2 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %39 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %40 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %41 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %42 = constant %41 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 4 : i64} : <>, <i64>
    %43:2 = fork [2] %42 {handshake.bb = 2 : ui32, handshake.name = "fork12"} : <i64>
    %44 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %45 = constant %44 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 3 : i64} : <>, <i64>
    %46:2 = fork [2] %45 {handshake.bb = 2 : ui32, handshake.name = "fork13"} : <i64>
    %47 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %48 = constant %47 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 2 : i64} : <>, <i64>
    %49:2 = fork [2] %48 {handshake.bb = 2 : ui32, handshake.name = "fork14"} : <i64>
    %50 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %51 = constant %50 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = 1 : i64} : <>, <i64>
    %52:2 = fork [2] %51 {handshake.bb = 2 : ui32, handshake.name = "fork15"} : <i64>
    %53 = shli %31#0, %52#1 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %54 = trunci %53 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i64> to <i10>
    %55 = shli %31#1, %49#1 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %56 = trunci %55 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i64> to <i10>
    %57 = addi %54, %56 {handshake.bb = 2 : ui32, handshake.name = "addi4"} : <i10>
    %58 = shli %31#2, %46#1 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %59 = trunci %58 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i64> to <i10>
    %60 = shli %31#3, %43#1 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i64>
    %61 = trunci %60 {handshake.bb = 2 : ui32, handshake.name = "trunci3"} : <i64> to <i10>
    %62 = addi %59, %61 {handshake.bb = 2 : ui32, handshake.name = "addi5"} : <i10>
    %63 = addi %57, %62 {handshake.bb = 2 : ui32, handshake.name = "addi6"} : <i10>
    %64 = addi %63, %21 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i10>
    %addressResult, %dataResult = load[%64] %outputs {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %65 = subi %26#1, %dataResult {handshake.bb = 2 : ui32, handshake.name = "subi0"} : <i32>
    %66 = shli %35#0, %52#0 {handshake.bb = 2 : ui32, handshake.name = "shli4"} : <i64>
    %67 = trunci %66 {handshake.bb = 2 : ui32, handshake.name = "trunci4"} : <i64> to <i10>
    %68 = shli %35#1, %49#0 {handshake.bb = 2 : ui32, handshake.name = "shli5"} : <i64>
    %69 = trunci %68 {handshake.bb = 2 : ui32, handshake.name = "trunci5"} : <i64> to <i10>
    %70 = addi %67, %69 {handshake.bb = 2 : ui32, handshake.name = "addi7"} : <i10>
    %71 = shli %35#2, %46#0 {handshake.bb = 2 : ui32, handshake.name = "shli6"} : <i64>
    %72 = trunci %71 {handshake.bb = 2 : ui32, handshake.name = "trunci6"} : <i64> to <i10>
    %73 = shli %35#3, %43#0 {handshake.bb = 2 : ui32, handshake.name = "shli7"} : <i64>
    %74 = trunci %73 {handshake.bb = 2 : ui32, handshake.name = "trunci7"} : <i64> to <i10>
    %75 = addi %72, %74 {handshake.bb = 2 : ui32, handshake.name = "addi8"} : <i10>
    %76 = addi %70, %75 {handshake.bb = 2 : ui32, handshake.name = "addi9"} : <i10>
    %77 = addi %76, %22 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i10>
    %addressResult_2, %dataResult_3 = store[%77] %65 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store1"} : <i10>, <i32>, <i10>, <i32>
    %78 = addi %23, %24 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i6>
    %79:2 = fork [2] %78 {handshake.bb = 2 : ui32, handshake.name = "fork16"} : <i6>
    %80 = trunci %79#0 {handshake.bb = 2 : ui32, handshake.name = "trunci8"} : <i6> to <i5>
    %81 = constant %39 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 30 : i6} : <>, <i6>
    %82 = cmpi ult, %79#1, %81 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i6>
    %83:6 = fork [6] %82 {handshake.bb = 2 : ui32, handshake.name = "fork17"} : <i1>
    %trueResult, %falseResult = cond_br %83#0, %80 {handshake.bb = 2 : ui32, handshake.name = "cond_br2"} : <i1>, <i5>
    sink %falseResult {handshake.name = "sink0"} : <i5>
    %trueResult_4, %falseResult_5 = cond_br %83#4, %26#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %83#3, %27 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i5>
    %trueResult_8, %falseResult_9 = cond_br %83#1, %29#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i5>
    sink %falseResult_9 {handshake.name = "sink1"} : <i5>
    %trueResult_10, %falseResult_11 = cond_br %83#2, %33#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i5>
    sink %falseResult_11 {handshake.name = "sink2"} : <i5>
    %trueResult_12, %falseResult_13 = cond_br %83#5, %37#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %84 = merge %falseResult_5 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %85 = merge %falseResult_7 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i5>
    %86 = extui %85 {handshake.bb = 3 : ui32, handshake.name = "extui11"} : <i5> to <i6>
    %87 = constant %89 {handshake.bb = 3 : ui32, handshake.name = "constant7", value = 1 : i6} : <>, <i6>
    %result_14, %index_15 = control_merge [%falseResult_13]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_15 {handshake.name = "sink3"} : <i1>
    %88 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %89 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %90 = addi %86, %87 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i6>
    %91:2 = fork [2] %90 {handshake.bb = 3 : ui32, handshake.name = "fork18"} : <i6>
    %92 = trunci %91#0 {handshake.bb = 3 : ui32, handshake.name = "trunci9"} : <i6> to <i5>
    %93 = constant %88 {handshake.bb = 3 : ui32, handshake.name = "constant17", value = 30 : i6} : <>, <i6>
    %94 = cmpi ult, %91#1, %93 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i6>
    %95:3 = fork [3] %94 {handshake.bb = 3 : ui32, handshake.name = "fork19"} : <i1>
    %trueResult_16, %falseResult_17 = cond_br %95#0, %92 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <i5>
    sink %falseResult_17 {handshake.name = "sink4"} : <i5>
    %trueResult_18, %falseResult_19 = cond_br %95#1, %84 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    sink %falseResult_19 {handshake.name = "sink5"} : <i32>
    %trueResult_20, %falseResult_21 = cond_br %95#2, %result_14 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %result_22, %index_23 = control_merge [%falseResult_21]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_23 {handshake.name = "sink6"} : <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %memEnd, %0#1 : <>, <>
  }
}

