module {
  handshake.func @gaussian(%arg0: memref<20xi32>, %arg1: memref<400xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["c", "a", "c_start", "a_start", "start"], resNames = ["out0", "c_end", "a_end", "end"]} {
    %0:3 = fork [3] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:3 = lsq[%arg1 : memref<400xi32>] (%arg3, %70#0, %addressResult, %addressResult_18, %addressResult_20, %dataResult_21, %116#1)  {groupSizes = [3 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i9>, !handshake.channel<i9>, !handshake.channel<i9>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %outputs, %memEnd = mem_controller[%arg0 : memref<20xi32>] %arg2 (%addressResult_16) %116#0 {connectedBlocks = [4 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i5>) -> !handshake.channel<i32>
    %2 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = true} : <>, <i1>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %4 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui7"} : <i1> to <i5>
    %5 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %6 = mux %index [%4, %trueResult_40] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i5>, <i5>] to <i5>
    %7:2 = fork [2] %6 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i5>
    %8 = extui %7#1 {handshake.bb = 1 : ui32, handshake.name = "extui8"} : <i5> to <i6>
    %9 = constant %11 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i6} : <>, <i6>
    %result, %index = control_merge [%5, %trueResult_42]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %10 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %11 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %12 = addi %8, %9 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i6>
    %13:2 = fork [2] %12 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i6>
    %14 = trunci %13#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i6> to <i5>
    %15 = constant %10 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 19 : i6} : <>, <i6>
    %16 = cmpi ult, %13#1, %15 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i6>
    %17:3 = fork [3] %16 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i1>
    %trueResult, %falseResult = cond_br %17#0, %14 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i5>
    sink %falseResult {handshake.name = "sink0"} : <i5>
    %trueResult_0, %falseResult_1 = cond_br %17#1, %7#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i5>
    %trueResult_2, %falseResult_3 = cond_br %17#2, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %18 = merge %falseResult_25 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i5>
    %19 = merge %falseResult_27 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i5>
    %20 = extui %19 {handshake.bb = 2 : ui32, handshake.name = "extui9"} : <i5> to <i6>
    %21 = constant %23 {handshake.bb = 2 : ui32, handshake.name = "constant4", value = 1 : i6} : <>, <i6>
    %result_4, %index_5 = control_merge [%falseResult_37]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_5 {handshake.name = "sink1"} : <i1>
    %22 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %23 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %24 = addi %20, %21 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i6>
    %25:2 = fork [2] %24 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i6>
    %26 = trunci %25#0 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i6> to <i5>
    %27 = constant %22 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 19 : i6} : <>, <i6>
    %28 = cmpi ult, %25#1, %27 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i6>
    %29:3 = fork [3] %28 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i1>
    %trueResult_6, %falseResult_7 = cond_br %29#0, %26 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i5>
    sink %falseResult_7 {handshake.name = "sink2"} : <i5>
    %trueResult_8, %falseResult_9 = cond_br %29#1, %18 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i5>
    %trueResult_10, %falseResult_11 = cond_br %29#2, %result_4 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %30 = mux %34#1 [%trueResult, %trueResult_6] {handshake.bb = 3 : ui32, handshake.name = "mux1"} : <i1>, [<i5>, <i5>] to <i5>
    %31:3 = fork [3] %30 {handshake.bb = 3 : ui32, handshake.name = "fork6"} : <i5>
    %32 = mux %34#0 [%trueResult_0, %trueResult_8] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i5>, <i5>] to <i5>
    %33:3 = fork [3] %32 {handshake.bb = 3 : ui32, handshake.name = "fork7"} : <i5>
    %result_12, %index_13 = control_merge [%trueResult_2, %trueResult_10]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %34:2 = fork [2] %index_13 {handshake.bb = 3 : ui32, handshake.name = "fork8"} : <i1>
    %35:2 = fork [2] %result_12 {handshake.bb = 3 : ui32, handshake.name = "fork9"} : <>
    %36 = constant %35#0 {handshake.bb = 3 : ui32, handshake.name = "constant6", value = true} : <>, <i1>
    %37 = br %36 {handshake.bb = 3 : ui32, handshake.name = "br4"} : <i1>
    %38 = extui %37 {handshake.bb = 4 : ui32, handshake.name = "extui10"} : <i1> to <i5>
    %39 = br %33#2 {handshake.bb = 3 : ui32, handshake.name = "br5"} : <i5>
    %40 = br %31#2 {handshake.bb = 3 : ui32, handshake.name = "br6"} : <i5>
    %41 = br %31#0 {handshake.bb = 3 : ui32, handshake.name = "br7"} : <i5>
    %42 = br %33#0 {handshake.bb = 3 : ui32, handshake.name = "br8"} : <i5>
    %43 = br %33#1 {handshake.bb = 3 : ui32, handshake.name = "br9"} : <i5>
    %44 = br %31#1 {handshake.bb = 3 : ui32, handshake.name = "br10"} : <i5>
    %45 = br %35#1 {handshake.bb = 3 : ui32, handshake.name = "br11"} : <>
    %46 = mux %69#6 [%38, %trueResult_22] {handshake.bb = 4 : ui32, handshake.name = "mux3"} : <i1>, [<i5>, <i5>] to <i5>
    %47:4 = fork [4] %46 {handshake.bb = 4 : ui32, handshake.name = "fork10"} : <i5>
    %48 = extui %47#0 {handshake.bb = 4 : ui32, handshake.name = "extui11"} : <i5> to <i9>
    %49 = extui %47#1 {handshake.bb = 4 : ui32, handshake.name = "extui12"} : <i5> to <i9>
    %50 = extui %47#2 {handshake.bb = 4 : ui32, handshake.name = "extui13"} : <i5> to <i9>
    %51 = extui %47#3 {handshake.bb = 4 : ui32, handshake.name = "extui14"} : <i5> to <i6>
    %52 = constant %72 {handshake.bb = 4 : ui32, handshake.name = "constant19", value = 1 : i6} : <>, <i6>
    %53 = mux %69#2 [%39, %trueResult_24] {handshake.bb = 4 : ui32, handshake.name = "mux4"} : <i1>, [<i5>, <i5>] to <i5>
    %54 = mux %69#5 [%40, %trueResult_26] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i5>, <i5>] to <i5>
    %55 = mux %69#3 [%41, %trueResult_28] {handshake.bb = 4 : ui32, handshake.name = "mux6"} : <i1>, [<i5>, <i5>] to <i5>
    %56:2 = fork [2] %55 {handshake.bb = 4 : ui32, handshake.name = "fork11"} : <i5>
    %57 = extui %56#1 {handshake.bb = 4 : ui32, handshake.name = "extui15"} : <i5> to <i64>
    %58:2 = fork [2] %57 {handshake.bb = 4 : ui32, handshake.name = "fork12"} : <i64>
    %59 = mux %69#0 [%42, %trueResult_30] {handshake.bb = 4 : ui32, handshake.name = "mux7"} : <i1>, [<i5>, <i5>] to <i5>
    %60:2 = fork [2] %59 {handshake.bb = 4 : ui32, handshake.name = "fork13"} : <i5>
    %61 = mux %69#1 [%43, %trueResult_32] {handshake.bb = 4 : ui32, handshake.name = "mux8"} : <i1>, [<i5>, <i5>] to <i5>
    %62:2 = fork [2] %61 {handshake.bb = 4 : ui32, handshake.name = "fork14"} : <i5>
    %63 = extui %62#1 {handshake.bb = 4 : ui32, handshake.name = "extui16"} : <i5> to <i64>
    %64:2 = fork [2] %63 {handshake.bb = 4 : ui32, handshake.name = "fork15"} : <i64>
    %65 = mux %69#4 [%44, %trueResult_34] {handshake.bb = 4 : ui32, handshake.name = "mux9"} : <i1>, [<i5>, <i5>] to <i5>
    %66:2 = fork [2] %65 {handshake.bb = 4 : ui32, handshake.name = "fork16"} : <i5>
    %67 = extui %66#1 {handshake.bb = 4 : ui32, handshake.name = "extui17"} : <i5> to <i64>
    %68:2 = fork [2] %67 {handshake.bb = 4 : ui32, handshake.name = "fork17"} : <i64>
    %result_14, %index_15 = control_merge [%45, %trueResult_36]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %69:7 = fork [7] %index_15 {handshake.bb = 4 : ui32, handshake.name = "fork18"} : <i1>
    %70:2 = fork [2] %result_14 {handshake.bb = 4 : ui32, handshake.name = "fork19"} : <>
    %71 = source {handshake.bb = 4 : ui32, handshake.name = "source4"} : <>
    %72 = source {handshake.bb = 4 : ui32, handshake.name = "source5"} : <>
    %73 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %74 = constant %73 {handshake.bb = 4 : ui32, handshake.name = "constant14", value = 4 : i64} : <>, <i64>
    %75:3 = fork [3] %74 {handshake.bb = 4 : ui32, handshake.name = "fork20"} : <i64>
    %76 = source {handshake.bb = 4 : ui32, handshake.name = "source7"} : <>
    %77 = constant %76 {handshake.bb = 4 : ui32, handshake.name = "constant15", value = 2 : i64} : <>, <i64>
    %78:3 = fork [3] %77 {handshake.bb = 4 : ui32, handshake.name = "fork21"} : <i64>
    %79 = shli %58#0, %78#2 {handshake.bb = 4 : ui32, handshake.name = "shli0"} : <i64>
    %80 = trunci %79 {handshake.bb = 4 : ui32, handshake.name = "trunci2"} : <i64> to <i9>
    %81 = shli %58#1, %75#2 {handshake.bb = 4 : ui32, handshake.name = "shli1"} : <i64>
    %82 = trunci %81 {handshake.bb = 4 : ui32, handshake.name = "trunci3"} : <i64> to <i9>
    %83 = addi %80, %82 {handshake.bb = 4 : ui32, handshake.name = "addi7"} : <i9>
    %84 = addi %83, %48 {handshake.bb = 4 : ui32, handshake.name = "addi2"} : <i9>
    %addressResult, %dataResult = load[%84] %1#0 {handshake.bb = 4 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : <i9>, <i32>, <i9>, <i32>
    %addressResult_16, %dataResult_17 = load[%60#0] %outputs {handshake.bb = 4 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i5>, <i32>, <i5>, <i32>
    %85 = shli %64#0, %78#1 {handshake.bb = 4 : ui32, handshake.name = "shli2"} : <i64>
    %86 = trunci %85 {handshake.bb = 4 : ui32, handshake.name = "trunci4"} : <i64> to <i9>
    %87 = shli %64#1, %75#1 {handshake.bb = 4 : ui32, handshake.name = "shli3"} : <i64>
    %88 = trunci %87 {handshake.bb = 4 : ui32, handshake.name = "trunci5"} : <i64> to <i9>
    %89 = addi %86, %88 {handshake.bb = 4 : ui32, handshake.name = "addi8"} : <i9>
    %90 = addi %89, %49 {handshake.bb = 4 : ui32, handshake.name = "addi3"} : <i9>
    %addressResult_18, %dataResult_19 = load[%90] %1#1 {handshake.bb = 4 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load2"} : <i9>, <i32>, <i9>, <i32>
    %91 = muli %dataResult_17, %dataResult_19 {handshake.bb = 4 : ui32, handshake.name = "muli2"} : <i32>
    %92 = subi %dataResult, %91 {handshake.bb = 4 : ui32, handshake.name = "subi0"} : <i32>
    %93 = shli %68#0, %78#0 {handshake.bb = 4 : ui32, handshake.name = "shli4"} : <i64>
    %94 = trunci %93 {handshake.bb = 4 : ui32, handshake.name = "trunci6"} : <i64> to <i9>
    %95 = shli %68#1, %75#0 {handshake.bb = 4 : ui32, handshake.name = "shli5"} : <i64>
    %96 = trunci %95 {handshake.bb = 4 : ui32, handshake.name = "trunci7"} : <i64> to <i9>
    %97 = addi %94, %96 {handshake.bb = 4 : ui32, handshake.name = "addi9"} : <i9>
    %98 = addi %97, %50 {handshake.bb = 4 : ui32, handshake.name = "addi4"} : <i9>
    %addressResult_20, %dataResult_21 = store[%98] %92 {handshake.bb = 4 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store3"} : <i9>, <i32>, <i9>, <i32>
    %99 = addi %51, %52 {handshake.bb = 4 : ui32, handshake.name = "addi5"} : <i6>
    %100:2 = fork [2] %99 {handshake.bb = 4 : ui32, handshake.name = "fork22"} : <i6>
    %101 = trunci %100#0 {handshake.bb = 4 : ui32, handshake.name = "trunci8"} : <i6> to <i5>
    %102 = constant %71 {handshake.bb = 4 : ui32, handshake.name = "constant20", value = 20 : i6} : <>, <i6>
    %103 = cmpi ult, %100#1, %102 {handshake.bb = 4 : ui32, handshake.name = "cmpi2"} : <i6>
    %104:8 = fork [8] %103 {handshake.bb = 4 : ui32, handshake.name = "fork23"} : <i1>
    %trueResult_22, %falseResult_23 = cond_br %104#0, %101 {handshake.bb = 4 : ui32, handshake.name = "cond_br10"} : <i1>, <i5>
    sink %falseResult_23 {handshake.name = "sink3"} : <i5>
    %trueResult_24, %falseResult_25 = cond_br %104#3, %53 {handshake.bb = 4 : ui32, handshake.name = "cond_br11"} : <i1>, <i5>
    %trueResult_26, %falseResult_27 = cond_br %104#6, %54 {handshake.bb = 4 : ui32, handshake.name = "cond_br12"} : <i1>, <i5>
    %trueResult_28, %falseResult_29 = cond_br %104#4, %56#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br13"} : <i1>, <i5>
    sink %falseResult_29 {handshake.name = "sink4"} : <i5>
    %trueResult_30, %falseResult_31 = cond_br %104#1, %60#1 {handshake.bb = 4 : ui32, handshake.name = "cond_br14"} : <i1>, <i5>
    sink %falseResult_31 {handshake.name = "sink5"} : <i5>
    %trueResult_32, %falseResult_33 = cond_br %104#2, %62#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br15"} : <i1>, <i5>
    sink %falseResult_33 {handshake.name = "sink6"} : <i5>
    %trueResult_34, %falseResult_35 = cond_br %104#5, %66#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br16"} : <i1>, <i5>
    sink %falseResult_35 {handshake.name = "sink7"} : <i5>
    %trueResult_36, %falseResult_37 = cond_br %104#7, %70#1 {handshake.bb = 4 : ui32, handshake.name = "cond_br17"} : <i1>, <>
    %105 = mux %index_39 [%falseResult_1, %falseResult_9] {handshake.bb = 5 : ui32, handshake.name = "mux10"} : <i1>, [<i5>, <i5>] to <i5>
    %106 = extui %105 {handshake.bb = 5 : ui32, handshake.name = "extui18"} : <i5> to <i6>
    %107 = constant %109 {handshake.bb = 5 : ui32, handshake.name = "constant21", value = 1 : i6} : <>, <i6>
    %result_38, %index_39 = control_merge [%falseResult_3, %falseResult_11]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %108 = source {handshake.bb = 5 : ui32, handshake.name = "source8"} : <>
    %109 = source {handshake.bb = 5 : ui32, handshake.name = "source9"} : <>
    %110 = addi %106, %107 {handshake.bb = 5 : ui32, handshake.name = "addi6"} : <i6>
    %111:2 = fork [2] %110 {handshake.bb = 5 : ui32, handshake.name = "fork24"} : <i6>
    %112 = trunci %111#0 {handshake.bb = 5 : ui32, handshake.name = "trunci9"} : <i6> to <i5>
    %113 = constant %108 {handshake.bb = 5 : ui32, handshake.name = "constant22", value = 19 : i6} : <>, <i6>
    %114 = cmpi ult, %111#1, %113 {handshake.bb = 5 : ui32, handshake.name = "cmpi3"} : <i6>
    %115:2 = fork [2] %114 {handshake.bb = 5 : ui32, handshake.name = "fork25"} : <i1>
    %trueResult_40, %falseResult_41 = cond_br %115#0, %112 {handshake.bb = 5 : ui32, handshake.name = "cond_br18"} : <i1>, <i5>
    sink %falseResult_41 {handshake.name = "sink8"} : <i5>
    %trueResult_42, %falseResult_43 = cond_br %115#1, %result_38 {handshake.bb = 5 : ui32, handshake.name = "cond_br19"} : <i1>, <>
    %result_44, %index_45 = control_merge [%falseResult_43]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    sink %index_45 {handshake.name = "sink9"} : <i1>
    %116:2 = fork [2] %result_44 {handshake.bb = 6 : ui32, handshake.name = "fork26"} : <>
    %117 = source {handshake.bb = 6 : ui32, handshake.name = "source10"} : <>
    %118 = constant %117 {handshake.bb = 6 : ui32, handshake.name = "constant18", value = 29070 : i32} : <>, <i32>
    end {handshake.bb = 6 : ui32, handshake.name = "end0"} %118, %memEnd, %1#2, %0#1 : <i32>, <>, <>, <>
  }
}

