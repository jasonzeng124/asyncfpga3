module {
  handshake.func @sobel(%arg0: memref<256xi32>, %arg1: memref<9xi32>, %arg2: memref<9xi32>, %arg3: memref<256xi32>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["in", "gX", "gY", "out", "in_start", "gX_start", "gY_start", "out_start", "start"], resNames = ["out0", "in_end", "gX_end", "gY_end", "out_end", "end"]} {
    %0:3 = fork [3] %arg8 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %memEnd = mem_controller[%arg3 : memref<256xi32>] %arg7 (%198, %addressResult_93, %dataResult_94) %225#3 {connectedBlocks = [10 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i32>, !handshake.channel<i8>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg2 : memref<9xi32>] %arg6 (%addressResult_41) %225#2 {connectedBlocks = [7 : i32], handshake.name = "mem_controller5"} :    (!handshake.channel<i4>) -> !handshake.channel<i32>
    %outputs_1, %memEnd_2 = mem_controller[%arg1 : memref<9xi32>] %arg5 (%addressResult_43) %225#1 {connectedBlocks = [7 : i32], handshake.name = "mem_controller6"} :    (!handshake.channel<i4>) -> !handshake.channel<i32>
    %outputs_3:2, %memEnd_4 = mem_controller[%arg0 : memref<256xi32>] %arg4 (%addressResult, %addressResult_35) %225#0 {connectedBlocks = [5 : i32], handshake.name = "mem_controller7"} :    (!handshake.channel<i8>, !handshake.channel<i8>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <i1>
    %3 = extui %2 {handshake.bb = 0 : ui32, handshake.name = "extui3"} : <i1> to <i32>
    %4:2 = fork [2] %3 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %5 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br6"} : <>
    %6 = mux %8#0 [%4#0, %trueResult_105] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %7 = mux %8#1 [%4#1, %trueResult_107] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%5, %trueResult_109]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %8:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i1>
    %9:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <>
    %10 = br %6 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i32>
    %11 = constant %9#0 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %12 = br %11 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i1>
    %13 = extui %12 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i1> to <i32>
    %14 = br %7 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <i32>
    %15 = br %9#1 {handshake.bb = 1 : ui32, handshake.name = "br10"} : <>
    %16 = mux %20#0 [%10, %trueResult_95] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %17 = mux %20#1 [%13, %trueResult_97] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %18:2 = fork [2] %17 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i32>
    %19 = mux %20#2 [%14, %trueResult_99] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %result_5, %index_6 = control_merge [%15, %trueResult_101]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %20:3 = fork [3] %index_6 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i1>
    %21 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %22 = constant %21 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 5 : i32} : <>, <i32>
    %23 = cmpi ult, %18#1, %22 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %24:4 = fork [4] %23 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i1>
    %trueResult, %falseResult = cond_br %24#3, %19 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_7, %falseResult_8 = cond_br %24#2, %16 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_9, %falseResult_10 = cond_br %24#1, %18#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %25 = trunci %trueResult_9 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i32> to <i3>
    %trueResult_11, %falseResult_12 = cond_br %24#0, %result_5 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %26 = merge %falseResult {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %27 = merge %falseResult_8 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i32>
    %28 = merge %falseResult_10 {handshake.bb = 3 : ui32, handshake.name = "merge2"} : <i32>
    %29:2 = fork [2] %28 {handshake.bb = 3 : ui32, handshake.name = "fork7"} : <i32>
    %result_13, %index_14 = control_merge [%falseResult_12]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_14 {handshake.name = "sink0"} : <i1>
    %30 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %31 = constant %30 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = 5 : i32} : <>, <i32>
    %32 = cmpi eq, %29#1, %31 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %33:4 = fork [4] %32 {handshake.bb = 3 : ui32, handshake.name = "fork8"} : <i1>
    %trueResult_15, %falseResult_16 = cond_br %33#3, %27 {handshake.bb = 3 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_17, %falseResult_18 = cond_br %33#2, %26 {handshake.bb = 3 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_19, %falseResult_20 = cond_br %33#1, %29#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %34 = trunci %trueResult_19 {handshake.bb = 3 : ui32, handshake.name = "trunci1"} : <i32> to <i3>
    %35 = extui %34 {handshake.bb = 3 : ui32, handshake.name = "extui5"} : <i3> to <i32>
    %trueResult_21, %falseResult_22 = cond_br %33#0, %result_13 {handshake.bb = 3 : ui32, handshake.name = "cond_br14"} : <i1>, <>
    %36 = merge %trueResult {handshake.bb = 4 : ui32, handshake.name = "merge3"} : <i32>
    %37 = merge %trueResult_7 {handshake.bb = 4 : ui32, handshake.name = "merge4"} : <i32>
    %38 = merge %25 {handshake.bb = 4 : ui32, handshake.name = "merge5"} : <i3>
    %39:2 = fork [2] %38 {handshake.bb = 4 : ui32, handshake.name = "fork9"} : <i3>
    %result_23, %index_24 = control_merge [%trueResult_11]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_24 {handshake.name = "sink1"} : <i1>
    %40 = source {handshake.bb = 4 : ui32, handshake.name = "source2"} : <>
    %41 = constant %40 {handshake.bb = 4 : ui32, handshake.name = "constant5", value = 0 : i3} : <>, <i3>
    %42 = cmpi eq, %39#1, %41 {handshake.bb = 4 : ui32, handshake.name = "cmpi2"} : <i3>
    %43:4 = fork [4] %42 {handshake.bb = 4 : ui32, handshake.name = "fork10"} : <i1>
    %trueResult_25, %falseResult_26 = cond_br %43#1, %37 {handshake.bb = 4 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %trueResult_27, %falseResult_28 = cond_br %43#2, %36 {handshake.bb = 4 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_29, %falseResult_30 = cond_br %43#0, %39#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br17"} : <i1>, <i3>
    %44 = extui %falseResult_30 {handshake.bb = 4 : ui32, handshake.name = "extui6"} : <i3> to <i32>
    %45 = trunci %trueResult_29 {handshake.bb = 4 : ui32, handshake.name = "trunci2"} : <i3> to <i1>
    %46 = extui %45 {handshake.bb = 4 : ui32, handshake.name = "extui7"} : <i1> to <i32>
    %trueResult_31, %falseResult_32 = cond_br %43#3, %result_23 {handshake.bb = 4 : ui32, handshake.name = "cond_br18"} : <i1>, <>
    %47 = mux %53#0 [%falseResult_18, %falseResult_28] {handshake.bb = 5 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %48 = mux %53#1 [%falseResult_16, %falseResult_26] {handshake.bb = 5 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %49 = mux %53#2 [%falseResult_20, %44] {handshake.bb = 5 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %50:3 = fork [3] %49 {handshake.bb = 5 : ui32, handshake.name = "fork11"} : <i32>
    %51 = trunci %50#0 {handshake.bb = 5 : ui32, handshake.name = "trunci3"} : <i32> to <i8>
    %52 = trunci %50#1 {handshake.bb = 5 : ui32, handshake.name = "trunci4"} : <i32> to <i8>
    %result_33, %index_34 = control_merge [%falseResult_22, %falseResult_32]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %53:3 = fork [3] %index_34 {handshake.bb = 5 : ui32, handshake.name = "fork12"} : <i1>
    %54:3 = fork [3] %result_33 {handshake.bb = 5 : ui32, handshake.name = "fork13"} : <>
    %addressResult, %dataResult = load[%52] %outputs_3#0 {handshake.bb = 5 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i8>, <i32>, <i8>, <i32>
    %addressResult_35, %dataResult_36 = load[%51] %outputs_3#1 {handshake.bb = 5 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i8>, <i32>, <i8>, <i32>
    %55 = constant %54#0 {handshake.bb = 5 : ui32, handshake.name = "constant6", value = true} : <>, <i1>
    %56 = br %55 {handshake.bb = 5 : ui32, handshake.name = "br11"} : <i1>
    %57 = extsi %56 {handshake.bb = 5 : ui32, handshake.name = "extsi0"} : <i1> to <i32>
    %58 = constant %54#1 {handshake.bb = 5 : ui32, handshake.name = "constant7", value = false} : <>, <i1>
    %59 = br %58 {handshake.bb = 5 : ui32, handshake.name = "br12"} : <i1>
    %60 = extui %59 {handshake.bb = 5 : ui32, handshake.name = "extui8"} : <i1> to <i32>
    %61:2 = fork [2] %60 {handshake.bb = 5 : ui32, handshake.name = "fork14"} : <i32>
    %62 = br %47 {handshake.bb = 5 : ui32, handshake.name = "br13"} : <i32>
    %63 = br %48 {handshake.bb = 5 : ui32, handshake.name = "br14"} : <i32>
    %64 = br %50#2 {handshake.bb = 5 : ui32, handshake.name = "br15"} : <i32>
    %65 = br %dataResult {handshake.bb = 5 : ui32, handshake.name = "br16"} : <i32>
    %66 = br %dataResult_36 {handshake.bb = 5 : ui32, handshake.name = "br17"} : <i32>
    %67 = br %54#2 {handshake.bb = 5 : ui32, handshake.name = "br18"} : <>
    %68 = mux %77#0 [%57, %trueResult_71] {handshake.bb = 6 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %69:5 = fork [5] %68 {handshake.bb = 6 : ui32, handshake.name = "fork15"} : <i32>
    %70 = mux %77#1 [%61#0, %trueResult_73] {handshake.bb = 6 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %71 = mux %77#2 [%61#1, %trueResult_75] {handshake.bb = 6 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %72 = mux %77#3 [%62, %trueResult_77] {handshake.bb = 6 : ui32, handshake.name = "mux11"} : <i1>, [<i32>, <i32>] to <i32>
    %73 = mux %77#4 [%63, %trueResult_79] {handshake.bb = 6 : ui32, handshake.name = "mux12"} : <i1>, [<i32>, <i32>] to <i32>
    %74 = mux %77#5 [%64, %trueResult_81] {handshake.bb = 6 : ui32, handshake.name = "mux13"} : <i1>, [<i32>, <i32>] to <i32>
    %75 = mux %77#6 [%65, %trueResult_83] {handshake.bb = 6 : ui32, handshake.name = "mux14"} : <i1>, [<i32>, <i32>] to <i32>
    %76 = mux %77#7 [%66, %trueResult_85] {handshake.bb = 6 : ui32, handshake.name = "mux15"} : <i1>, [<i32>, <i32>] to <i32>
    %result_37, %index_38 = control_merge [%67, %trueResult_87]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>, <>] to <>, <i1>
    %77:8 = fork [8] %index_38 {handshake.bb = 6 : ui32, handshake.name = "fork16"} : <i1>
    %78:2 = fork [2] %result_37 {handshake.bb = 6 : ui32, handshake.name = "fork17"} : <>
    %79 = source {handshake.bb = 6 : ui32, handshake.name = "source3"} : <>
    %80 = constant %79 {handshake.bb = 6 : ui32, handshake.name = "constant15", value = 1 : i32} : <>, <i32>
    %81:2 = fork [2] %80 {handshake.bb = 6 : ui32, handshake.name = "fork18"} : <i32>
    %82 = shli %69#4, %81#1 {handshake.bb = 6 : ui32, handshake.name = "shli0"} : <i32>
    %83 = addi %69#3, %82 {handshake.bb = 6 : ui32, handshake.name = "addi13"} : <i32>
    %84 = shli %69#2, %81#0 {handshake.bb = 6 : ui32, handshake.name = "shli1"} : <i32>
    %85 = addi %69#1, %84 {handshake.bb = 6 : ui32, handshake.name = "addi14"} : <i32>
    %86 = constant %78#0 {handshake.bb = 6 : ui32, handshake.name = "constant8", value = true} : <>, <i1>
    %87 = br %86 {handshake.bb = 6 : ui32, handshake.name = "br19"} : <i1>
    %88 = extsi %87 {handshake.bb = 6 : ui32, handshake.name = "extsi1"} : <i1> to <i32>
    %89 = br %70 {handshake.bb = 6 : ui32, handshake.name = "br20"} : <i32>
    %90 = br %71 {handshake.bb = 6 : ui32, handshake.name = "br21"} : <i32>
    %91 = br %72 {handshake.bb = 6 : ui32, handshake.name = "br22"} : <i32>
    %92 = br %73 {handshake.bb = 6 : ui32, handshake.name = "br23"} : <i32>
    %93 = br %74 {handshake.bb = 6 : ui32, handshake.name = "br24"} : <i32>
    %94 = br %75 {handshake.bb = 6 : ui32, handshake.name = "br25"} : <i32>
    %95 = br %76 {handshake.bb = 6 : ui32, handshake.name = "br26"} : <i32>
    %96 = br %69#0 {handshake.bb = 6 : ui32, handshake.name = "br27"} : <i32>
    %97 = br %83 {handshake.bb = 6 : ui32, handshake.name = "br28"} : <i32>
    %98 = br %85 {handshake.bb = 6 : ui32, handshake.name = "br29"} : <i32>
    %99 = br %78#1 {handshake.bb = 6 : ui32, handshake.name = "br30"} : <>
    %100 = mux %120#0 [%88, %trueResult_45] {handshake.bb = 7 : ui32, handshake.name = "mux16"} : <i1>, [<i32>, <i32>] to <i32>
    %101:3 = fork [3] %100 {handshake.bb = 7 : ui32, handshake.name = "fork19"} : <i32>
    %102 = trunci %101#0 {handshake.bb = 7 : ui32, handshake.name = "trunci5"} : <i32> to <i4>
    %103 = trunci %101#1 {handshake.bb = 7 : ui32, handshake.name = "trunci6"} : <i32> to <i4>
    %104 = mux %120#1 [%89, %trueResult_47] {handshake.bb = 7 : ui32, handshake.name = "mux17"} : <i1>, [<i32>, <i32>] to <i32>
    %105 = mux %120#2 [%90, %trueResult_49] {handshake.bb = 7 : ui32, handshake.name = "mux18"} : <i1>, [<i32>, <i32>] to <i32>
    %106 = mux %120#3 [%91, %trueResult_51] {handshake.bb = 7 : ui32, handshake.name = "mux19"} : <i1>, [<i32>, <i32>] to <i32>
    %107 = mux %120#4 [%92, %trueResult_53] {handshake.bb = 7 : ui32, handshake.name = "mux20"} : <i1>, [<i32>, <i32>] to <i32>
    %108 = mux %120#5 [%93, %trueResult_55] {handshake.bb = 7 : ui32, handshake.name = "mux21"} : <i1>, [<i32>, <i32>] to <i32>
    %109 = mux %120#6 [%94, %trueResult_57] {handshake.bb = 7 : ui32, handshake.name = "mux22"} : <i1>, [<i32>, <i32>] to <i32>
    %110:2 = fork [2] %109 {handshake.bb = 7 : ui32, handshake.name = "fork20"} : <i32>
    %111 = mux %120#7 [%95, %trueResult_59] {handshake.bb = 7 : ui32, handshake.name = "mux23"} : <i1>, [<i32>, <i32>] to <i32>
    %112:2 = fork [2] %111 {handshake.bb = 7 : ui32, handshake.name = "fork21"} : <i32>
    %113 = mux %120#8 [%96, %trueResult_61] {handshake.bb = 7 : ui32, handshake.name = "mux24"} : <i1>, [<i32>, <i32>] to <i32>
    %114 = mux %120#9 [%97, %trueResult_63] {handshake.bb = 7 : ui32, handshake.name = "mux25"} : <i1>, [<i32>, <i32>] to <i32>
    %115:2 = fork [2] %114 {handshake.bb = 7 : ui32, handshake.name = "fork22"} : <i32>
    %116 = trunci %115#0 {handshake.bb = 7 : ui32, handshake.name = "trunci7"} : <i32> to <i4>
    %117 = mux %120#10 [%98, %trueResult_65] {handshake.bb = 7 : ui32, handshake.name = "mux26"} : <i1>, [<i32>, <i32>] to <i32>
    %118:2 = fork [2] %117 {handshake.bb = 7 : ui32, handshake.name = "fork23"} : <i32>
    %119 = trunci %118#0 {handshake.bb = 7 : ui32, handshake.name = "trunci8"} : <i32> to <i4>
    %result_39, %index_40 = control_merge [%99, %trueResult_67]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>, <>] to <>, <i1>
    %120:11 = fork [11] %index_40 {handshake.bb = 7 : ui32, handshake.name = "fork24"} : <i1>
    %121 = source {handshake.bb = 7 : ui32, handshake.name = "source4"} : <>
    %122 = constant %121 {handshake.bb = 7 : ui32, handshake.name = "constant17", value = 2 : i32} : <>, <i32>
    %123 = source {handshake.bb = 7 : ui32, handshake.name = "source5"} : <>
    %124 = constant %123 {handshake.bb = 7 : ui32, handshake.name = "constant18", value = 1 : i32} : <>, <i32>
    %125 = source {handshake.bb = 7 : ui32, handshake.name = "source6"} : <>
    %126:2 = fork [2] %125 {handshake.bb = 7 : ui32, handshake.name = "fork25"} : <>
    %127 = addi %116, %102 {handshake.bb = 7 : ui32, handshake.name = "addi0"} : <i4>
    %128 = constant %126#0 {handshake.bb = 7 : ui32, handshake.name = "constant29", value = 4 : i4} : <>, <i4>
    %129 = addi %127, %128 {handshake.bb = 7 : ui32, handshake.name = "addi1"} : <i4>
    %addressResult_41, %dataResult_42 = load[%129] %outputs {handshake.bb = 7 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load2"} : <i4>, <i32>, <i4>, <i32>
    %130 = muli %110#1, %dataResult_42 {handshake.bb = 7 : ui32, handshake.name = "muli2"} : <i32>
    %131 = addi %104, %130 {handshake.bb = 7 : ui32, handshake.name = "addi2"} : <i32>
    %132 = addi %119, %103 {handshake.bb = 7 : ui32, handshake.name = "addi3"} : <i4>
    %133 = constant %126#1 {handshake.bb = 7 : ui32, handshake.name = "constant30", value = 4 : i4} : <>, <i4>
    %134 = addi %132, %133 {handshake.bb = 7 : ui32, handshake.name = "addi4"} : <i4>
    %addressResult_43, %dataResult_44 = load[%134] %outputs_1 {handshake.bb = 7 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load3"} : <i4>, <i32>, <i4>, <i32>
    %135 = muli %112#1, %dataResult_44 {handshake.bb = 7 : ui32, handshake.name = "muli3"} : <i32>
    %136 = addi %105, %135 {handshake.bb = 7 : ui32, handshake.name = "addi5"} : <i32>
    %137 = addi %101#2, %124 {handshake.bb = 7 : ui32, handshake.name = "addi6"} : <i32>
    %138:2 = fork [2] %137 {handshake.bb = 7 : ui32, handshake.name = "fork26"} : <i32>
    %139 = cmpi ne, %138#1, %122 {handshake.bb = 7 : ui32, handshake.name = "cmpi3"} : <i32>
    %140:12 = fork [12] %139 {handshake.bb = 7 : ui32, handshake.name = "fork27"} : <i1>
    %trueResult_45, %falseResult_46 = cond_br %140#11, %138#0 {handshake.bb = 7 : ui32, handshake.name = "cond_br19"} : <i1>, <i32>
    sink %falseResult_46 {handshake.name = "sink2"} : <i32>
    %trueResult_47, %falseResult_48 = cond_br %140#10, %131 {handshake.bb = 7 : ui32, handshake.name = "cond_br20"} : <i1>, <i32>
    %trueResult_49, %falseResult_50 = cond_br %140#9, %136 {handshake.bb = 7 : ui32, handshake.name = "cond_br21"} : <i1>, <i32>
    %trueResult_51, %falseResult_52 = cond_br %140#8, %106 {handshake.bb = 7 : ui32, handshake.name = "cond_br22"} : <i1>, <i32>
    %trueResult_53, %falseResult_54 = cond_br %140#7, %107 {handshake.bb = 7 : ui32, handshake.name = "cond_br23"} : <i1>, <i32>
    %trueResult_55, %falseResult_56 = cond_br %140#6, %108 {handshake.bb = 7 : ui32, handshake.name = "cond_br24"} : <i1>, <i32>
    %trueResult_57, %falseResult_58 = cond_br %140#5, %110#0 {handshake.bb = 7 : ui32, handshake.name = "cond_br25"} : <i1>, <i32>
    %trueResult_59, %falseResult_60 = cond_br %140#4, %112#0 {handshake.bb = 7 : ui32, handshake.name = "cond_br26"} : <i1>, <i32>
    %trueResult_61, %falseResult_62 = cond_br %140#3, %113 {handshake.bb = 7 : ui32, handshake.name = "cond_br27"} : <i1>, <i32>
    %trueResult_63, %falseResult_64 = cond_br %140#2, %115#1 {handshake.bb = 7 : ui32, handshake.name = "cond_br28"} : <i1>, <i32>
    sink %falseResult_64 {handshake.name = "sink3"} : <i32>
    %trueResult_65, %falseResult_66 = cond_br %140#1, %118#1 {handshake.bb = 7 : ui32, handshake.name = "cond_br29"} : <i1>, <i32>
    sink %falseResult_66 {handshake.name = "sink4"} : <i32>
    %trueResult_67, %falseResult_68 = cond_br %140#0, %result_39 {handshake.bb = 7 : ui32, handshake.name = "cond_br30"} : <i1>, <>
    %141 = merge %falseResult_50 {handshake.bb = 8 : ui32, handshake.name = "merge6"} : <i32>
    %142 = merge %falseResult_48 {handshake.bb = 8 : ui32, handshake.name = "merge7"} : <i32>
    %143 = merge %falseResult_52 {handshake.bb = 8 : ui32, handshake.name = "merge8"} : <i32>
    %144 = merge %falseResult_54 {handshake.bb = 8 : ui32, handshake.name = "merge9"} : <i32>
    %145 = merge %falseResult_56 {handshake.bb = 8 : ui32, handshake.name = "merge10"} : <i32>
    %146 = merge %falseResult_58 {handshake.bb = 8 : ui32, handshake.name = "merge11"} : <i32>
    %147 = merge %falseResult_60 {handshake.bb = 8 : ui32, handshake.name = "merge12"} : <i32>
    %148 = merge %falseResult_62 {handshake.bb = 8 : ui32, handshake.name = "merge13"} : <i32>
    %result_69, %index_70 = control_merge [%falseResult_68]  {handshake.bb = 8 : ui32, handshake.name = "control_merge7"} : [<>] to <>, <i1>
    sink %index_70 {handshake.name = "sink5"} : <i1>
    %149 = source {handshake.bb = 8 : ui32, handshake.name = "source7"} : <>
    %150 = constant %149 {handshake.bb = 8 : ui32, handshake.name = "constant20", value = 2 : i32} : <>, <i32>
    %151 = source {handshake.bb = 8 : ui32, handshake.name = "source8"} : <>
    %152 = constant %151 {handshake.bb = 8 : ui32, handshake.name = "constant21", value = 1 : i32} : <>, <i32>
    %153 = addi %148, %152 {handshake.bb = 8 : ui32, handshake.name = "addi7"} : <i32>
    %154:2 = fork [2] %153 {handshake.bb = 8 : ui32, handshake.name = "fork28"} : <i32>
    %155 = cmpi ne, %154#1, %150 {handshake.bb = 8 : ui32, handshake.name = "cmpi4"} : <i32>
    %156:9 = fork [9] %155 {handshake.bb = 8 : ui32, handshake.name = "fork29"} : <i1>
    %trueResult_71, %falseResult_72 = cond_br %156#8, %154#0 {handshake.bb = 8 : ui32, handshake.name = "cond_br31"} : <i1>, <i32>
    sink %falseResult_72 {handshake.name = "sink6"} : <i32>
    %trueResult_73, %falseResult_74 = cond_br %156#7, %142 {handshake.bb = 8 : ui32, handshake.name = "cond_br32"} : <i1>, <i32>
    %trueResult_75, %falseResult_76 = cond_br %156#6, %141 {handshake.bb = 8 : ui32, handshake.name = "cond_br33"} : <i1>, <i32>
    %trueResult_77, %falseResult_78 = cond_br %156#5, %143 {handshake.bb = 8 : ui32, handshake.name = "cond_br34"} : <i1>, <i32>
    %trueResult_79, %falseResult_80 = cond_br %156#4, %144 {handshake.bb = 8 : ui32, handshake.name = "cond_br35"} : <i1>, <i32>
    %trueResult_81, %falseResult_82 = cond_br %156#3, %145 {handshake.bb = 8 : ui32, handshake.name = "cond_br36"} : <i1>, <i32>
    %trueResult_83, %falseResult_84 = cond_br %156#2, %146 {handshake.bb = 8 : ui32, handshake.name = "cond_br37"} : <i1>, <i32>
    sink %falseResult_84 {handshake.name = "sink7"} : <i32>
    %trueResult_85, %falseResult_86 = cond_br %156#1, %147 {handshake.bb = 8 : ui32, handshake.name = "cond_br38"} : <i1>, <i32>
    sink %falseResult_86 {handshake.name = "sink8"} : <i32>
    %trueResult_87, %falseResult_88 = cond_br %156#0, %result_69 {handshake.bb = 8 : ui32, handshake.name = "cond_br39"} : <i1>, <>
    %157 = merge %falseResult_76 {handshake.bb = 9 : ui32, handshake.name = "merge14"} : <i32>
    %158:2 = fork [2] %157 {handshake.bb = 9 : ui32, handshake.name = "fork30"} : <i32>
    %159 = merge %falseResult_74 {handshake.bb = 9 : ui32, handshake.name = "merge15"} : <i32>
    %160:2 = fork [2] %159 {handshake.bb = 9 : ui32, handshake.name = "fork31"} : <i32>
    %161 = merge %falseResult_78 {handshake.bb = 9 : ui32, handshake.name = "merge16"} : <i32>
    %162 = merge %falseResult_80 {handshake.bb = 9 : ui32, handshake.name = "merge17"} : <i32>
    %163 = merge %falseResult_82 {handshake.bb = 9 : ui32, handshake.name = "merge18"} : <i32>
    %result_89, %index_90 = control_merge [%falseResult_88]  {handshake.bb = 9 : ui32, handshake.name = "control_merge8"} : [<>] to <>, <i1>
    sink %index_90 {handshake.name = "sink9"} : <i1>
    %164 = source {handshake.bb = 9 : ui32, handshake.name = "source9"} : <>
    %165 = constant %164 {handshake.bb = 9 : ui32, handshake.name = "constant22", value = 255 : i32} : <>, <i32>
    %166:4 = fork [4] %165 {handshake.bb = 9 : ui32, handshake.name = "fork32"} : <i32>
    %167 = source {handshake.bb = 9 : ui32, handshake.name = "source10"} : <>
    %168 = constant %167 {handshake.bb = 9 : ui32, handshake.name = "constant23", value = 0 : i32} : <>, <i32>
    %169:4 = fork [4] %168 {handshake.bb = 9 : ui32, handshake.name = "fork33"} : <i32>
    %170 = cmpi sgt, %158#1, %166#3 {handshake.bb = 9 : ui32, handshake.name = "cmpi5"} : <i32>
    %171 = select %170[%166#2, %158#0] {handshake.bb = 9 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %172:2 = fork [2] %171 {handshake.bb = 9 : ui32, handshake.name = "fork34"} : <i32>
    %173 = cmpi slt, %172#1, %169#3 {handshake.bb = 9 : ui32, handshake.name = "cmpi6"} : <i32>
    %174 = select %173[%169#2, %172#0] {handshake.bb = 9 : ui32, handshake.name = "select1"} : <i1>, <i32>
    %175 = cmpi sgt, %160#1, %166#1 {handshake.bb = 9 : ui32, handshake.name = "cmpi7"} : <i32>
    %176 = select %175[%166#0, %160#0] {handshake.bb = 9 : ui32, handshake.name = "select2"} : <i1>, <i32>
    %177:2 = fork [2] %176 {handshake.bb = 9 : ui32, handshake.name = "fork35"} : <i32>
    %178 = cmpi slt, %177#1, %169#1 {handshake.bb = 9 : ui32, handshake.name = "cmpi8"} : <i32>
    %179 = select %178[%169#0, %177#0] {handshake.bb = 9 : ui32, handshake.name = "select3"} : <i1>, <i32>
    %180 = addi %174, %179 {handshake.bb = 9 : ui32, handshake.name = "addi8"} : <i32>
    %181 = addi %162, %180 {handshake.bb = 9 : ui32, handshake.name = "addi9"} : <i32>
    %182 = br %181 {handshake.bb = 9 : ui32, handshake.name = "br31"} : <i32>
    %183 = br %161 {handshake.bb = 9 : ui32, handshake.name = "br32"} : <i32>
    %184 = br %163 {handshake.bb = 9 : ui32, handshake.name = "br33"} : <i32>
    %185 = br %result_89 {handshake.bb = 9 : ui32, handshake.name = "br34"} : <>
    %186 = mux %196#0 [%trueResult_15, %trueResult_25, %182] {handshake.bb = 10 : ui32, handshake.name = "mux27"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %187:2 = fork [2] %186 {handshake.bb = 10 : ui32, handshake.name = "fork36"} : <i32>
    %188 = trunci %187#0 {handshake.bb = 10 : ui32, handshake.name = "trunci9"} : <i32> to <i8>
    %189 = constant %202#1 {handshake.bb = 10 : ui32, handshake.name = "constant31", value = -1 : i8} : <>, <i8>
    %190 = mux %196#1 [%trueResult_17, %trueResult_27, %183] {handshake.bb = 10 : ui32, handshake.name = "mux28"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %191:2 = fork [2] %190 {handshake.bb = 10 : ui32, handshake.name = "fork37"} : <i32>
    %192 = trunci %191#0 {handshake.bb = 10 : ui32, handshake.name = "trunci10"} : <i32> to <i8>
    %193 = mux %196#2 [%35, %46, %184] {handshake.bb = 10 : ui32, handshake.name = "mux29"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %194:2 = fork [2] %193 {handshake.bb = 10 : ui32, handshake.name = "fork38"} : <i32>
    %195 = trunci %194#0 {handshake.bb = 10 : ui32, handshake.name = "trunci11"} : <i32> to <i8>
    %result_91, %index_92 = control_merge [%trueResult_21, %trueResult_31, %185]  {handshake.bb = 10 : ui32, handshake.name = "control_merge9"} : [<>, <>, <>] to <>, <i2>
    %196:3 = fork [3] %index_92 {handshake.bb = 10 : ui32, handshake.name = "fork39"} : <i2>
    %197:2 = fork [2] %result_91 {handshake.bb = 10 : ui32, handshake.name = "fork40"} : <>
    %198 = constant %197#0 {handshake.bb = 10 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %199 = source {handshake.bb = 10 : ui32, handshake.name = "source11"} : <>
    %200 = constant %199 {handshake.bb = 10 : ui32, handshake.name = "constant24", value = 15 : i32} : <>, <i32>
    %201 = source {handshake.bb = 10 : ui32, handshake.name = "source12"} : <>
    %202:2 = fork [2] %201 {handshake.bb = 10 : ui32, handshake.name = "fork41"} : <>
    %203 = source {handshake.bb = 10 : ui32, handshake.name = "source13"} : <>
    %204 = constant %203 {handshake.bb = 10 : ui32, handshake.name = "constant26", value = 1 : i32} : <>, <i32>
    %205 = andi %188, %189 {handshake.bb = 10 : ui32, handshake.name = "andi0"} : <i8>
    %206 = constant %202#0 {handshake.bb = 10 : ui32, handshake.name = "constant32", value = -1 : i8} : <>, <i8>
    %207 = xori %205, %206 {handshake.bb = 10 : ui32, handshake.name = "xori0"} : <i8>
    %208 = extui %207 {handshake.bb = 10 : ui32, handshake.name = "extui9"} : <i8> to <i32>
    %209 = addi %195, %192 {handshake.bb = 10 : ui32, handshake.name = "addi10"} : <i8>
    %addressResult_93, %dataResult_94 = store[%209] %208 {handshake.bb = 10 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store4"} : <i8>, <i32>, <i8>, <i32>
    %210 = addi %194#1, %204 {handshake.bb = 10 : ui32, handshake.name = "addi11"} : <i32>
    %211:2 = fork [2] %210 {handshake.bb = 10 : ui32, handshake.name = "fork42"} : <i32>
    %212 = cmpi ne, %211#1, %200 {handshake.bb = 10 : ui32, handshake.name = "cmpi9"} : <i32>
    %213:4 = fork [4] %212 {handshake.bb = 10 : ui32, handshake.name = "fork43"} : <i1>
    %trueResult_95, %falseResult_96 = cond_br %213#3, %187#1 {handshake.bb = 10 : ui32, handshake.name = "cond_br40"} : <i1>, <i32>
    %trueResult_97, %falseResult_98 = cond_br %213#2, %211#0 {handshake.bb = 10 : ui32, handshake.name = "cond_br41"} : <i1>, <i32>
    sink %falseResult_98 {handshake.name = "sink10"} : <i32>
    %trueResult_99, %falseResult_100 = cond_br %213#1, %191#1 {handshake.bb = 10 : ui32, handshake.name = "cond_br42"} : <i1>, <i32>
    %trueResult_101, %falseResult_102 = cond_br %213#0, %197#1 {handshake.bb = 10 : ui32, handshake.name = "cond_br43"} : <i1>, <>
    %214 = merge %falseResult_96 {handshake.bb = 11 : ui32, handshake.name = "merge19"} : <i32>
    %215 = merge %falseResult_100 {handshake.bb = 11 : ui32, handshake.name = "merge20"} : <i32>
    %result_103, %index_104 = control_merge [%falseResult_102]  {handshake.bb = 11 : ui32, handshake.name = "control_merge10"} : [<>] to <>, <i1>
    sink %index_104 {handshake.name = "sink11"} : <i1>
    %216 = source {handshake.bb = 11 : ui32, handshake.name = "source14"} : <>
    %217 = constant %216 {handshake.bb = 11 : ui32, handshake.name = "constant27", value = 15 : i32} : <>, <i32>
    %218 = source {handshake.bb = 11 : ui32, handshake.name = "source15"} : <>
    %219 = constant %218 {handshake.bb = 11 : ui32, handshake.name = "constant28", value = 1 : i32} : <>, <i32>
    %220 = addi %215, %219 {handshake.bb = 11 : ui32, handshake.name = "addi12"} : <i32>
    %221:2 = fork [2] %220 {handshake.bb = 11 : ui32, handshake.name = "fork44"} : <i32>
    %222 = cmpi ne, %221#1, %217 {handshake.bb = 11 : ui32, handshake.name = "cmpi10"} : <i32>
    %223:3 = fork [3] %222 {handshake.bb = 11 : ui32, handshake.name = "fork45"} : <i1>
    %trueResult_105, %falseResult_106 = cond_br %223#2, %214 {handshake.bb = 11 : ui32, handshake.name = "cond_br44"} : <i1>, <i32>
    %trueResult_107, %falseResult_108 = cond_br %223#1, %221#0 {handshake.bb = 11 : ui32, handshake.name = "cond_br45"} : <i1>, <i32>
    sink %falseResult_108 {handshake.name = "sink12"} : <i32>
    %trueResult_109, %falseResult_110 = cond_br %223#0, %result_103 {handshake.bb = 11 : ui32, handshake.name = "cond_br46"} : <i1>, <>
    %224 = merge %falseResult_106 {handshake.bb = 12 : ui32, handshake.name = "merge21"} : <i32>
    %result_111, %index_112 = control_merge [%falseResult_110]  {handshake.bb = 12 : ui32, handshake.name = "control_merge11"} : [<>] to <>, <i1>
    sink %index_112 {handshake.name = "sink13"} : <i1>
    %225:4 = fork [4] %result_111 {handshake.bb = 12 : ui32, handshake.name = "fork46"} : <>
    end {handshake.bb = 12 : ui32, handshake.name = "end0"} %224, %memEnd_4, %memEnd_2, %memEnd_0, %memEnd, %0#1 : <i32>, <>, <>, <>, <>, <>
  }
}

