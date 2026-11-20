module {
  handshake.func @video_filter(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: memref<900xi32>, %arg3: memref<900xi32>, %arg4: memref<900xi32>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["offset", "scale", "pixelR", "pixelG", "pixelB", "pixelR_start", "pixelG_start", "pixelB_start", "start"], resNames = ["pixelR_end", "pixelG_end", "pixelB_end", "end"]} {
    %0:3 = fork [3] %arg8 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg4 : memref<900xi32>] %arg7 (%65, %addressResult_8, %addressResult_10, %dataResult_11) %183#2 {connectedBlocks = [2 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i10>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_0, %memEnd_1 = mem_controller[%arg3 : memref<900xi32>] %arg6 (%66, %addressResult_12, %addressResult_14, %dataResult_15) %183#1 {connectedBlocks = [2 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i10>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_2, %memEnd_3 = mem_controller[%arg2 : memref<900xi32>] %arg5 (%67, %addressResult, %addressResult_6, %dataResult_7) %183#0 {connectedBlocks = [2 : i32], handshake.name = "mem_controller5"} :    (!handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i10>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant7", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %3 = extui %2 {handshake.bb = 0 : ui32, handshake.name = "extui12"} : <i1> to <i32>
    %4 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %5 = br %arg1 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <i32>
    %6 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <>
    %7 = mux %11#0 [%3, %trueResult_38] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %8:7 = fork [7] %7 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i32>
    %9 = mux %11#1 [%4, %trueResult_40] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %10 = mux %11#2 [%5, %trueResult_42] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%6, %trueResult_44]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %11:3 = fork [3] %index {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i1>
    %12:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <>
    %13 = constant %12#0 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = false} : <>, <i1>
    %14 = br %13 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i1>
    %15 = extui %14 {handshake.bb = 1 : ui32, handshake.name = "extui13"} : <i1> to <i32>
    %16 = br %9 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i32>
    %17 = br %10 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i32>
    %18 = br %8#6 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <i32>
    %19 = br %8#0 {handshake.bb = 1 : ui32, handshake.name = "br10"} : <i32>
    %20 = br %8#1 {handshake.bb = 1 : ui32, handshake.name = "br11"} : <i32>
    %21 = br %8#2 {handshake.bb = 1 : ui32, handshake.name = "br12"} : <i32>
    %22 = br %8#3 {handshake.bb = 1 : ui32, handshake.name = "br13"} : <i32>
    %23 = br %8#4 {handshake.bb = 1 : ui32, handshake.name = "br14"} : <i32>
    %24 = br %8#5 {handshake.bb = 1 : ui32, handshake.name = "br15"} : <i32>
    %25 = br %12#1 {handshake.bb = 1 : ui32, handshake.name = "br16"} : <>
    %26 = mux %63#6 [%15, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %27:7 = fork [7] %26 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i32>
    %28 = trunci %27#0 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i32> to <i10>
    %29 = trunci %27#1 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i32> to <i10>
    %30 = trunci %27#2 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i32> to <i10>
    %31 = trunci %27#3 {handshake.bb = 2 : ui32, handshake.name = "trunci3"} : <i32> to <i10>
    %32 = trunci %27#4 {handshake.bb = 2 : ui32, handshake.name = "trunci4"} : <i32> to <i10>
    %33 = trunci %27#5 {handshake.bb = 2 : ui32, handshake.name = "trunci5"} : <i32> to <i10>
    %34 = mux %63#7 [%16, %trueResult_16] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %35:4 = fork [4] %34 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i32>
    %36 = mux %63#8 [%17, %trueResult_18] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %37:4 = fork [4] %36 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i32>
    %38 = mux %63#9 [%18, %trueResult_20] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %39 = mux %63#0 [%19, %trueResult_22] {handshake.bb = 2 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %40:2 = fork [2] %39 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i32>
    %41 = extui %40#1 {handshake.bb = 2 : ui32, handshake.name = "extui14"} : <i32> to <i64>
    %42:4 = fork [4] %41 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i64>
    %43 = mux %63#1 [%20, %trueResult_24] {handshake.bb = 2 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %44:2 = fork [2] %43 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i32>
    %45 = extui %44#1 {handshake.bb = 2 : ui32, handshake.name = "extui15"} : <i32> to <i64>
    %46:4 = fork [4] %45 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <i64>
    %47 = mux %63#2 [%21, %trueResult_26] {handshake.bb = 2 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %48:2 = fork [2] %47 {handshake.bb = 2 : ui32, handshake.name = "fork11"} : <i32>
    %49 = extui %48#1 {handshake.bb = 2 : ui32, handshake.name = "extui16"} : <i32> to <i64>
    %50:4 = fork [4] %49 {handshake.bb = 2 : ui32, handshake.name = "fork12"} : <i64>
    %51 = mux %63#3 [%22, %trueResult_28] {handshake.bb = 2 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %52:2 = fork [2] %51 {handshake.bb = 2 : ui32, handshake.name = "fork13"} : <i32>
    %53 = extui %52#1 {handshake.bb = 2 : ui32, handshake.name = "extui17"} : <i32> to <i64>
    %54:4 = fork [4] %53 {handshake.bb = 2 : ui32, handshake.name = "fork14"} : <i64>
    %55 = mux %63#4 [%23, %trueResult_30] {handshake.bb = 2 : ui32, handshake.name = "mux11"} : <i1>, [<i32>, <i32>] to <i32>
    %56:2 = fork [2] %55 {handshake.bb = 2 : ui32, handshake.name = "fork15"} : <i32>
    %57 = extui %56#1 {handshake.bb = 2 : ui32, handshake.name = "extui18"} : <i32> to <i64>
    %58:4 = fork [4] %57 {handshake.bb = 2 : ui32, handshake.name = "fork16"} : <i64>
    %59 = mux %63#5 [%24, %trueResult_32] {handshake.bb = 2 : ui32, handshake.name = "mux12"} : <i1>, [<i32>, <i32>] to <i32>
    %60:2 = fork [2] %59 {handshake.bb = 2 : ui32, handshake.name = "fork17"} : <i32>
    %61 = extui %60#1 {handshake.bb = 2 : ui32, handshake.name = "extui19"} : <i32> to <i64>
    %62:4 = fork [4] %61 {handshake.bb = 2 : ui32, handshake.name = "fork18"} : <i64>
    %result_4, %index_5 = control_merge [%25, %trueResult_34]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %63:10 = fork [10] %index_5 {handshake.bb = 2 : ui32, handshake.name = "fork19"} : <i1>
    %64:4 = fork [4] %result_4 {handshake.bb = 2 : ui32, handshake.name = "fork20"} : <>
    %65 = constant %64#0 {handshake.bb = 2 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %66 = constant %64#1 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %67 = constant %64#2 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %68 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %69 = constant %68 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 30 : i32} : <>, <i32>
    %70 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %71 = constant %70 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 1 : i32} : <>, <i32>
    %72 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %73 = constant %72 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 4 : i32} : <>, <i32>
    %74:3 = fork [3] %73 {handshake.bb = 2 : ui32, handshake.name = "fork21"} : <i32>
    %75 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %76 = constant %75 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 4 : i64} : <>, <i64>
    %77:6 = fork [6] %76 {handshake.bb = 2 : ui32, handshake.name = "fork22"} : <i64>
    %78 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %79 = constant %78 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = 3 : i64} : <>, <i64>
    %80:6 = fork [6] %79 {handshake.bb = 2 : ui32, handshake.name = "fork23"} : <i64>
    %81 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %82 = constant %81 {handshake.bb = 2 : ui32, handshake.name = "constant15", value = 2 : i64} : <>, <i64>
    %83:6 = fork [6] %82 {handshake.bb = 2 : ui32, handshake.name = "fork24"} : <i64>
    %84 = source {handshake.bb = 2 : ui32, handshake.name = "source6"} : <>
    %85 = constant %84 {handshake.bb = 2 : ui32, handshake.name = "constant16", value = 1 : i64} : <>, <i64>
    %86:6 = fork [6] %85 {handshake.bb = 2 : ui32, handshake.name = "fork25"} : <i64>
    %87 = shli %42#0, %86#5 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %88 = trunci %87 {handshake.bb = 2 : ui32, handshake.name = "trunci6"} : <i64> to <i10>
    %89 = shli %42#1, %83#5 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %90 = trunci %89 {handshake.bb = 2 : ui32, handshake.name = "trunci7"} : <i64> to <i10>
    %91 = addi %88, %90 {handshake.bb = 2 : ui32, handshake.name = "addi8"} : <i10>
    %92 = shli %42#2, %80#5 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %93 = trunci %92 {handshake.bb = 2 : ui32, handshake.name = "trunci8"} : <i64> to <i10>
    %94 = shli %42#3, %77#5 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i64>
    %95 = trunci %94 {handshake.bb = 2 : ui32, handshake.name = "trunci9"} : <i64> to <i10>
    %96 = addi %93, %95 {handshake.bb = 2 : ui32, handshake.name = "addi9"} : <i10>
    %97 = addi %91, %96 {handshake.bb = 2 : ui32, handshake.name = "addi10"} : <i10>
    %98 = addi %97, %28 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i10>
    %addressResult, %dataResult = load[%98] %outputs_2 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %99 = subi %dataResult, %35#3 {handshake.bb = 2 : ui32, handshake.name = "subi0"} : <i32>
    %100 = muli %99, %37#3 {handshake.bb = 2 : ui32, handshake.name = "muli1"} : <i32>
    %101 = shrsi %100, %74#2 {handshake.bb = 2 : ui32, handshake.name = "shrsi0"} : <i32>
    %102 = shli %46#0, %86#4 {handshake.bb = 2 : ui32, handshake.name = "shli4"} : <i64>
    %103 = trunci %102 {handshake.bb = 2 : ui32, handshake.name = "trunci10"} : <i64> to <i10>
    %104 = shli %46#1, %83#4 {handshake.bb = 2 : ui32, handshake.name = "shli5"} : <i64>
    %105 = trunci %104 {handshake.bb = 2 : ui32, handshake.name = "trunci11"} : <i64> to <i10>
    %106 = addi %103, %105 {handshake.bb = 2 : ui32, handshake.name = "addi11"} : <i10>
    %107 = shli %46#2, %80#4 {handshake.bb = 2 : ui32, handshake.name = "shli6"} : <i64>
    %108 = trunci %107 {handshake.bb = 2 : ui32, handshake.name = "trunci12"} : <i64> to <i10>
    %109 = shli %46#3, %77#4 {handshake.bb = 2 : ui32, handshake.name = "shli7"} : <i64>
    %110 = trunci %109 {handshake.bb = 2 : ui32, handshake.name = "trunci13"} : <i64> to <i10>
    %111 = addi %108, %110 {handshake.bb = 2 : ui32, handshake.name = "addi12"} : <i10>
    %112 = addi %106, %111 {handshake.bb = 2 : ui32, handshake.name = "addi13"} : <i10>
    %113 = addi %112, %29 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i10>
    %addressResult_6, %dataResult_7 = store[%113] %101 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store1"} : <i10>, <i32>, <i10>, <i32>
    %114 = shli %50#0, %86#3 {handshake.bb = 2 : ui32, handshake.name = "shli8"} : <i64>
    %115 = trunci %114 {handshake.bb = 2 : ui32, handshake.name = "trunci14"} : <i64> to <i10>
    %116 = shli %50#1, %83#3 {handshake.bb = 2 : ui32, handshake.name = "shli9"} : <i64>
    %117 = trunci %116 {handshake.bb = 2 : ui32, handshake.name = "trunci15"} : <i64> to <i10>
    %118 = addi %115, %117 {handshake.bb = 2 : ui32, handshake.name = "addi14"} : <i10>
    %119 = shli %50#2, %80#3 {handshake.bb = 2 : ui32, handshake.name = "shli10"} : <i64>
    %120 = trunci %119 {handshake.bb = 2 : ui32, handshake.name = "trunci16"} : <i64> to <i10>
    %121 = shli %50#3, %77#3 {handshake.bb = 2 : ui32, handshake.name = "shli11"} : <i64>
    %122 = trunci %121 {handshake.bb = 2 : ui32, handshake.name = "trunci17"} : <i64> to <i10>
    %123 = addi %120, %122 {handshake.bb = 2 : ui32, handshake.name = "addi15"} : <i10>
    %124 = addi %118, %123 {handshake.bb = 2 : ui32, handshake.name = "addi16"} : <i10>
    %125 = addi %124, %30 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i10>
    %addressResult_8, %dataResult_9 = load[%125] %outputs {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load2"} : <i10>, <i32>, <i10>, <i32>
    %126 = subi %dataResult_9, %35#2 {handshake.bb = 2 : ui32, handshake.name = "subi1"} : <i32>
    %127 = muli %126, %37#2 {handshake.bb = 2 : ui32, handshake.name = "muli4"} : <i32>
    %128 = shrsi %127, %74#1 {handshake.bb = 2 : ui32, handshake.name = "shrsi1"} : <i32>
    %129 = shli %54#0, %86#2 {handshake.bb = 2 : ui32, handshake.name = "shli12"} : <i64>
    %130 = trunci %129 {handshake.bb = 2 : ui32, handshake.name = "trunci18"} : <i64> to <i10>
    %131 = shli %54#1, %83#2 {handshake.bb = 2 : ui32, handshake.name = "shli13"} : <i64>
    %132 = trunci %131 {handshake.bb = 2 : ui32, handshake.name = "trunci19"} : <i64> to <i10>
    %133 = addi %130, %132 {handshake.bb = 2 : ui32, handshake.name = "addi17"} : <i10>
    %134 = shli %54#2, %80#2 {handshake.bb = 2 : ui32, handshake.name = "shli14"} : <i64>
    %135 = trunci %134 {handshake.bb = 2 : ui32, handshake.name = "trunci20"} : <i64> to <i10>
    %136 = shli %54#3, %77#2 {handshake.bb = 2 : ui32, handshake.name = "shli15"} : <i64>
    %137 = trunci %136 {handshake.bb = 2 : ui32, handshake.name = "trunci21"} : <i64> to <i10>
    %138 = addi %135, %137 {handshake.bb = 2 : ui32, handshake.name = "addi18"} : <i10>
    %139 = addi %133, %138 {handshake.bb = 2 : ui32, handshake.name = "addi19"} : <i10>
    %140 = addi %139, %31 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i10>
    %addressResult_10, %dataResult_11 = store[%140] %128 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store3"} : <i10>, <i32>, <i10>, <i32>
    %141 = shli %58#0, %86#1 {handshake.bb = 2 : ui32, handshake.name = "shli16"} : <i64>
    %142 = trunci %141 {handshake.bb = 2 : ui32, handshake.name = "trunci22"} : <i64> to <i10>
    %143 = shli %58#1, %83#1 {handshake.bb = 2 : ui32, handshake.name = "shli17"} : <i64>
    %144 = trunci %143 {handshake.bb = 2 : ui32, handshake.name = "trunci23"} : <i64> to <i10>
    %145 = addi %142, %144 {handshake.bb = 2 : ui32, handshake.name = "addi20"} : <i10>
    %146 = shli %58#2, %80#1 {handshake.bb = 2 : ui32, handshake.name = "shli18"} : <i64>
    %147 = trunci %146 {handshake.bb = 2 : ui32, handshake.name = "trunci24"} : <i64> to <i10>
    %148 = shli %58#3, %77#1 {handshake.bb = 2 : ui32, handshake.name = "shli19"} : <i64>
    %149 = trunci %148 {handshake.bb = 2 : ui32, handshake.name = "trunci25"} : <i64> to <i10>
    %150 = addi %147, %149 {handshake.bb = 2 : ui32, handshake.name = "addi21"} : <i10>
    %151 = addi %145, %150 {handshake.bb = 2 : ui32, handshake.name = "addi22"} : <i10>
    %152 = addi %151, %32 {handshake.bb = 2 : ui32, handshake.name = "addi4"} : <i10>
    %addressResult_12, %dataResult_13 = load[%152] %outputs_0 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load4"} : <i10>, <i32>, <i10>, <i32>
    %153 = subi %dataResult_13, %35#1 {handshake.bb = 2 : ui32, handshake.name = "subi2"} : <i32>
    %154 = muli %153, %37#1 {handshake.bb = 2 : ui32, handshake.name = "muli7"} : <i32>
    %155 = shrsi %154, %74#0 {handshake.bb = 2 : ui32, handshake.name = "shrsi2"} : <i32>
    %156 = shli %62#0, %86#0 {handshake.bb = 2 : ui32, handshake.name = "shli20"} : <i64>
    %157 = trunci %156 {handshake.bb = 2 : ui32, handshake.name = "trunci26"} : <i64> to <i10>
    %158 = shli %62#1, %83#0 {handshake.bb = 2 : ui32, handshake.name = "shli21"} : <i64>
    %159 = trunci %158 {handshake.bb = 2 : ui32, handshake.name = "trunci27"} : <i64> to <i10>
    %160 = addi %157, %159 {handshake.bb = 2 : ui32, handshake.name = "addi23"} : <i10>
    %161 = shli %62#2, %80#0 {handshake.bb = 2 : ui32, handshake.name = "shli22"} : <i64>
    %162 = trunci %161 {handshake.bb = 2 : ui32, handshake.name = "trunci28"} : <i64> to <i10>
    %163 = shli %62#3, %77#0 {handshake.bb = 2 : ui32, handshake.name = "shli23"} : <i64>
    %164 = trunci %163 {handshake.bb = 2 : ui32, handshake.name = "trunci29"} : <i64> to <i10>
    %165 = addi %162, %164 {handshake.bb = 2 : ui32, handshake.name = "addi24"} : <i10>
    %166 = addi %160, %165 {handshake.bb = 2 : ui32, handshake.name = "addi25"} : <i10>
    %167 = addi %166, %33 {handshake.bb = 2 : ui32, handshake.name = "addi5"} : <i10>
    %addressResult_14, %dataResult_15 = store[%167] %155 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store5"} : <i10>, <i32>, <i10>, <i32>
    %168 = addi %27#6, %71 {handshake.bb = 2 : ui32, handshake.name = "addi6"} : <i32>
    %169:2 = fork [2] %168 {handshake.bb = 2 : ui32, handshake.name = "fork26"} : <i32>
    %170 = cmpi ne, %169#1, %69 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %171:11 = fork [11] %170 {handshake.bb = 2 : ui32, handshake.name = "fork27"} : <i1>
    %trueResult, %falseResult = cond_br %171#10, %169#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    sink %falseResult {handshake.name = "sink0"} : <i32>
    %trueResult_16, %falseResult_17 = cond_br %171#9, %35#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %171#8, %37#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %171#7, %38 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %171#0, %40#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    sink %falseResult_23 {handshake.name = "sink1"} : <i32>
    %trueResult_24, %falseResult_25 = cond_br %171#1, %44#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_25 {handshake.name = "sink2"} : <i32>
    %trueResult_26, %falseResult_27 = cond_br %171#2, %48#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    sink %falseResult_27 {handshake.name = "sink3"} : <i32>
    %trueResult_28, %falseResult_29 = cond_br %171#3, %52#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    sink %falseResult_29 {handshake.name = "sink4"} : <i32>
    %trueResult_30, %falseResult_31 = cond_br %171#4, %56#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    sink %falseResult_31 {handshake.name = "sink5"} : <i32>
    %trueResult_32, %falseResult_33 = cond_br %171#5, %60#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    sink %falseResult_33 {handshake.name = "sink6"} : <i32>
    %trueResult_34, %falseResult_35 = cond_br %171#6, %64#3 {handshake.bb = 2 : ui32, handshake.name = "cond_br12"} : <i1>, <>
    %172 = merge %falseResult_17 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %173 = merge %falseResult_19 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i32>
    %174 = merge %falseResult_21 {handshake.bb = 3 : ui32, handshake.name = "merge2"} : <i32>
    %result_36, %index_37 = control_merge [%falseResult_35]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_37 {handshake.name = "sink7"} : <i1>
    %175 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %176 = constant %175 {handshake.bb = 3 : ui32, handshake.name = "constant17", value = 30 : i32} : <>, <i32>
    %177 = source {handshake.bb = 3 : ui32, handshake.name = "source8"} : <>
    %178 = constant %177 {handshake.bb = 3 : ui32, handshake.name = "constant18", value = 1 : i32} : <>, <i32>
    %179 = addi %174, %178 {handshake.bb = 3 : ui32, handshake.name = "addi7"} : <i32>
    %180:2 = fork [2] %179 {handshake.bb = 3 : ui32, handshake.name = "fork28"} : <i32>
    %181 = cmpi ne, %180#1, %176 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %182:4 = fork [4] %181 {handshake.bb = 3 : ui32, handshake.name = "fork29"} : <i1>
    %trueResult_38, %falseResult_39 = cond_br %182#3, %180#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    sink %falseResult_39 {handshake.name = "sink8"} : <i32>
    %trueResult_40, %falseResult_41 = cond_br %182#2, %172 {handshake.bb = 3 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    sink %falseResult_41 {handshake.name = "sink9"} : <i32>
    %trueResult_42, %falseResult_43 = cond_br %182#1, %173 {handshake.bb = 3 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    sink %falseResult_43 {handshake.name = "sink10"} : <i32>
    %trueResult_44, %falseResult_45 = cond_br %182#0, %result_36 {handshake.bb = 3 : ui32, handshake.name = "cond_br16"} : <i1>, <>
    %result_46, %index_47 = control_merge [%falseResult_45]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_47 {handshake.name = "sink11"} : <i1>
    %183:3 = fork [3] %result_46 {handshake.bb = 4 : ui32, handshake.name = "fork30"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %memEnd_3, %memEnd_1, %memEnd, %0#1 : <>, <>, <>, <>
  }
}

