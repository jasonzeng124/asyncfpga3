module {
  handshake.func @gcd(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["a", "b", "start"], resNames = ["out0", "end"]} {
    %0:2 = fork [2] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg0 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %3 = constant %2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %4 = cmpi eq, %1#1, %3 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %5:3 = fork [3] %4 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %trueResult, %falseResult = cond_br %5#2, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %5#1, %0#1 {handshake.bb = 0 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %5#0, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    sink %trueResult_2 {handshake.name = "sink0"} : <i32>
    %6 = merge %falseResult_3 {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %7 = merge %falseResult {handshake.bb = 1 : ui32, handshake.name = "merge1"} : <i32>
    %8:2 = fork [2] %7 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %result, %index = control_merge [%falseResult_1]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    sink %index {handshake.name = "sink1"} : <i1>
    %9 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %10 = constant %9 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 0 : i32} : <>, <i32>
    %11 = cmpi eq, %8#1, %10 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %12:3 = fork [3] %11 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %trueResult_4, %falseResult_5 = cond_br %12#2, %6 {handshake.bb = 1 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %12#1, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br13"} : <i1>, <>
    %trueResult_8, %falseResult_9 = cond_br %12#0, %8#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    sink %trueResult_8 {handshake.name = "sink2"} : <i32>
    %13 = merge %falseResult_5 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %14:2 = fork [2] %13 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i32>
    %15 = merge %falseResult_9 {handshake.bb = 2 : ui32, handshake.name = "merge3"} : <i32>
    %16:2 = fork [2] %15 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i32>
    %result_10, %index_11 = control_merge [%falseResult_7]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_11 {handshake.name = "sink3"} : <i1>
    %17:3 = fork [3] %result_10 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <>
    %18 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %19 = ori %14#1, %16#1 {handshake.bb = 2 : ui32, handshake.name = "ori0"} : <i32>
    %20 = trunci %19 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i32> to <i1>
    %21 = constant %18 {handshake.bb = 2 : ui32, handshake.name = "constant1", value = true} : <>, <i1>
    %22 = andi %20, %21 {handshake.bb = 2 : ui32, handshake.name = "andi0"} : <i1>
    %23 = constant %17#0 {handshake.bb = 2 : ui32, handshake.name = "constant2", value = false} : <>, <i1>
    %24 = cmpi eq, %22, %23 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i1>
    %25:4 = fork [4] %24 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i1>
    %trueResult_12, %falseResult_13 = cond_br %25#0, %14#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %25#1, %16#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %26 = constant %17#1 {handshake.bb = 2 : ui32, handshake.name = "constant18", value = false} : <>, <i1>
    %trueResult_16, %falseResult_17 = cond_br %25#3, %26 {handshake.bb = 2 : ui32, handshake.name = "cond_br17"} : <i1>, <i1>
    %27 = extui %falseResult_17 {handshake.bb = 2 : ui32, handshake.name = "extui0"} : <i1> to <i32>
    %28 = extui %trueResult_16 {handshake.bb = 2 : ui32, handshake.name = "extui1"} : <i1> to <i32>
    %trueResult_18, %falseResult_19 = cond_br %25#2, %17#2 {handshake.bb = 2 : ui32, handshake.name = "cond_br18"} : <i1>, <>
    %29 = mux %32#0 [%trueResult_12, %trueResult_22] {handshake.bb = 3 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %30 = mux %32#1 [%trueResult_14, %trueResult_24] {handshake.bb = 3 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %31 = mux %32#2 [%28, %trueResult_26] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result_20, %index_21 = control_merge [%trueResult_18, %trueResult_28]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %32:3 = fork [3] %index_21 {handshake.bb = 3 : ui32, handshake.name = "fork9"} : <i1>
    %33 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %34:2 = fork [2] %33 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <>
    %35 = constant %34#1 {handshake.bb = 3 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %36:3 = fork [3] %35 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i32>
    %37 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %38 = shrsi %29, %36#2 {handshake.bb = 3 : ui32, handshake.name = "shrsi0"} : <i32>
    %39:2 = fork [2] %38 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <i32>
    %40 = shrsi %30, %36#1 {handshake.bb = 3 : ui32, handshake.name = "shrsi1"} : <i32>
    %41:2 = fork [2] %40 {handshake.bb = 3 : ui32, handshake.name = "fork13"} : <i32>
    %42 = addi %31, %36#0 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i32>
    %43 = ori %39#1, %41#1 {handshake.bb = 3 : ui32, handshake.name = "ori1"} : <i32>
    %44 = trunci %43 {handshake.bb = 3 : ui32, handshake.name = "trunci1"} : <i32> to <i1>
    %45 = constant %34#0 {handshake.bb = 3 : ui32, handshake.name = "constant19", value = true} : <>, <i1>
    %46 = andi %44, %45 {handshake.bb = 3 : ui32, handshake.name = "andi1"} : <i1>
    %47 = constant %37 {handshake.bb = 3 : ui32, handshake.name = "constant20", value = false} : <>, <i1>
    %48 = cmpi eq, %46, %47 {handshake.bb = 3 : ui32, handshake.name = "cmpi3"} : <i1>
    %49:4 = fork [4] %48 {handshake.bb = 3 : ui32, handshake.name = "fork14"} : <i1>
    %trueResult_22, %falseResult_23 = cond_br %49#0, %39#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br19"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %49#1, %41#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br20"} : <i1>, <i32>
    %trueResult_26, %falseResult_27 = cond_br %49#2, %42 {handshake.bb = 3 : ui32, handshake.name = "cond_br21"} : <i1>, <i32>
    %trueResult_28, %falseResult_29 = cond_br %49#3, %result_20 {handshake.bb = 3 : ui32, handshake.name = "cond_br22"} : <i1>, <>
    %50 = mux %53#0 [%27, %falseResult_27] {handshake.bb = 4 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %51 = mux %53#1 [%falseResult_15, %falseResult_25] {handshake.bb = 4 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %52 = mux %53#2 [%falseResult_13, %falseResult_23] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %result_30, %index_31 = control_merge [%falseResult_19, %falseResult_29]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %53:3 = fork [3] %index_31 {handshake.bb = 4 : ui32, handshake.name = "fork15"} : <i1>
    %54 = br %52 {handshake.bb = 4 : ui32, handshake.name = "br4"} : <i32>
    %55 = br %50 {handshake.bb = 4 : ui32, handshake.name = "br5"} : <i32>
    %56 = br %51 {handshake.bb = 4 : ui32, handshake.name = "br6"} : <i32>
    %57 = br %result_30 {handshake.bb = 4 : ui32, handshake.name = "br7"} : <>
    %58 = mux %64#0 [%54, %falseResult_43] {handshake.bb = 5 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %59:4 = fork [4] %58 {handshake.bb = 5 : ui32, handshake.name = "fork16"} : <i32>
    %60 = trunci %59#0 {handshake.bb = 5 : ui32, handshake.name = "trunci2"} : <i32> to <i1>
    %61 = constant %66#0 {handshake.bb = 5 : ui32, handshake.name = "constant21", value = true} : <>, <i1>
    %62 = mux %64#1 [%55, %falseResult_37] {handshake.bb = 5 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %63 = mux %64#2 [%56, %falseResult_39] {handshake.bb = 5 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %result_32, %index_33 = control_merge [%57, %falseResult_41]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %64:3 = fork [3] %index_33 {handshake.bb = 5 : ui32, handshake.name = "fork17"} : <i1>
    %65 = source {handshake.bb = 5 : ui32, handshake.name = "source5"} : <>
    %66:2 = fork [2] %65 {handshake.bb = 5 : ui32, handshake.name = "fork18"} : <>
    %67 = constant %66#1 {handshake.bb = 5 : ui32, handshake.name = "constant8", value = 1 : i32} : <>, <i32>
    %68:2 = fork [2] %67 {handshake.bb = 5 : ui32, handshake.name = "fork19"} : <i32>
    %69 = source {handshake.bb = 5 : ui32, handshake.name = "source6"} : <>
    %70 = cmpi slt, %59#3, %68#1 {handshake.bb = 5 : ui32, handshake.name = "cmpi4"} : <i32>
    %71 = andi %60, %61 {handshake.bb = 5 : ui32, handshake.name = "andi2"} : <i1>
    %72 = constant %69 {handshake.bb = 5 : ui32, handshake.name = "constant22", value = false} : <>, <i1>
    %73 = cmpi ne, %71, %72 {handshake.bb = 5 : ui32, handshake.name = "cmpi5"} : <i1>
    %74 = ori %73, %70 {handshake.bb = 5 : ui32, handshake.name = "ori2"} : <i1>
    %75:5 = fork [5] %74 {handshake.bb = 5 : ui32, handshake.name = "fork20"} : <i1>
    %76 = shrsi %59#2, %68#0 {handshake.bb = 5 : ui32, handshake.name = "shrsi2"} : <i32>
    %trueResult_34, %falseResult_35 = cond_br %75#4, %59#1 {handshake.bb = 5 : ui32, handshake.name = "cond_br23"} : <i1>, <i32>
    sink %falseResult_35 {handshake.name = "sink4"} : <i32>
    %trueResult_36, %falseResult_37 = cond_br %75#3, %62 {handshake.bb = 5 : ui32, handshake.name = "cond_br24"} : <i1>, <i32>
    %trueResult_38, %falseResult_39 = cond_br %75#2, %63 {handshake.bb = 5 : ui32, handshake.name = "cond_br25"} : <i1>, <i32>
    %trueResult_40, %falseResult_41 = cond_br %75#1, %result_32 {handshake.bb = 5 : ui32, handshake.name = "cond_br26"} : <i1>, <>
    %trueResult_42, %falseResult_43 = cond_br %75#0, %76 {handshake.bb = 5 : ui32, handshake.name = "cond_br27"} : <i1>, <i32>
    sink %trueResult_42 {handshake.name = "sink5"} : <i32>
    %77 = merge %trueResult_34 {handshake.bb = 6 : ui32, handshake.name = "merge4"} : <i32>
    %78 = merge %trueResult_36 {handshake.bb = 6 : ui32, handshake.name = "merge5"} : <i32>
    %79 = merge %trueResult_38 {handshake.bb = 6 : ui32, handshake.name = "merge6"} : <i32>
    %result_44, %index_45 = control_merge [%trueResult_40]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    sink %index_45 {handshake.name = "sink6"} : <i1>
    %80 = br %79 {handshake.bb = 6 : ui32, handshake.name = "br8"} : <i32>
    %81 = br %78 {handshake.bb = 6 : ui32, handshake.name = "br9"} : <i32>
    %82 = br %77 {handshake.bb = 6 : ui32, handshake.name = "br10"} : <i32>
    %83 = br %result_44 {handshake.bb = 6 : ui32, handshake.name = "br11"} : <>
    %84 = mux %90#0 [%80, %falseResult_57] {handshake.bb = 7 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %85:4 = fork [4] %84 {handshake.bb = 7 : ui32, handshake.name = "fork21"} : <i32>
    %86 = trunci %85#0 {handshake.bb = 7 : ui32, handshake.name = "trunci3"} : <i32> to <i1>
    %87 = constant %92#0 {handshake.bb = 7 : ui32, handshake.name = "constant23", value = true} : <>, <i1>
    %88 = mux %90#1 [%81, %falseResult_51] {handshake.bb = 7 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %89 = mux %90#2 [%82, %falseResult_53] {handshake.bb = 7 : ui32, handshake.name = "mux11"} : <i1>, [<i32>, <i32>] to <i32>
    %result_46, %index_47 = control_merge [%83, %falseResult_55]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>, <>] to <>, <i1>
    %90:3 = fork [3] %index_47 {handshake.bb = 7 : ui32, handshake.name = "fork22"} : <i1>
    %91 = source {handshake.bb = 7 : ui32, handshake.name = "source7"} : <>
    %92:2 = fork [2] %91 {handshake.bb = 7 : ui32, handshake.name = "fork23"} : <>
    %93 = constant %92#1 {handshake.bb = 7 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %94:2 = fork [2] %93 {handshake.bb = 7 : ui32, handshake.name = "fork24"} : <i32>
    %95 = source {handshake.bb = 7 : ui32, handshake.name = "source8"} : <>
    %96 = cmpi slt, %85#3, %94#1 {handshake.bb = 7 : ui32, handshake.name = "cmpi6"} : <i32>
    %97 = andi %86, %87 {handshake.bb = 7 : ui32, handshake.name = "andi3"} : <i1>
    %98 = constant %95 {handshake.bb = 7 : ui32, handshake.name = "constant24", value = false} : <>, <i1>
    %99 = cmpi ne, %97, %98 {handshake.bb = 7 : ui32, handshake.name = "cmpi7"} : <i1>
    %100 = ori %99, %96 {handshake.bb = 7 : ui32, handshake.name = "ori3"} : <i1>
    %101:5 = fork [5] %100 {handshake.bb = 7 : ui32, handshake.name = "fork25"} : <i1>
    %102 = shrsi %85#2, %94#0 {handshake.bb = 7 : ui32, handshake.name = "shrsi3"} : <i32>
    %trueResult_48, %falseResult_49 = cond_br %101#4, %85#1 {handshake.bb = 7 : ui32, handshake.name = "cond_br28"} : <i1>, <i32>
    sink %falseResult_49 {handshake.name = "sink7"} : <i32>
    %trueResult_50, %falseResult_51 = cond_br %101#3, %88 {handshake.bb = 7 : ui32, handshake.name = "cond_br29"} : <i1>, <i32>
    %trueResult_52, %falseResult_53 = cond_br %101#2, %89 {handshake.bb = 7 : ui32, handshake.name = "cond_br30"} : <i1>, <i32>
    %trueResult_54, %falseResult_55 = cond_br %101#1, %result_46 {handshake.bb = 7 : ui32, handshake.name = "cond_br31"} : <i1>, <>
    %trueResult_56, %falseResult_57 = cond_br %101#0, %102 {handshake.bb = 7 : ui32, handshake.name = "cond_br32"} : <i1>, <i32>
    sink %trueResult_56 {handshake.name = "sink8"} : <i32>
    %103 = merge %trueResult_48 {handshake.bb = 8 : ui32, handshake.name = "merge7"} : <i32>
    %104 = merge %trueResult_50 {handshake.bb = 8 : ui32, handshake.name = "merge8"} : <i32>
    %105 = merge %trueResult_52 {handshake.bb = 8 : ui32, handshake.name = "merge9"} : <i32>
    %106:2 = fork [2] %105 {handshake.bb = 8 : ui32, handshake.name = "fork26"} : <i32>
    %result_58, %index_59 = control_merge [%trueResult_54]  {handshake.bb = 8 : ui32, handshake.name = "control_merge7"} : [<>] to <>, <i1>
    sink %index_59 {handshake.name = "sink9"} : <i1>
    %107 = source {handshake.bb = 8 : ui32, handshake.name = "source9"} : <>
    %108 = constant %107 {handshake.bb = 8 : ui32, handshake.name = "constant12", value = 0 : i32} : <>, <i32>
    %109 = cmpi eq, %106#1, %108 {handshake.bb = 8 : ui32, handshake.name = "cmpi8"} : <i32>
    %110:4 = fork [4] %109 {handshake.bb = 8 : ui32, handshake.name = "fork27"} : <i1>
    %trueResult_60, %falseResult_61 = cond_br %110#3, %103 {handshake.bb = 8 : ui32, handshake.name = "cond_br33"} : <i1>, <i32>
    %trueResult_62, %falseResult_63 = cond_br %110#2, %104 {handshake.bb = 8 : ui32, handshake.name = "cond_br34"} : <i1>, <i32>
    %trueResult_64, %falseResult_65 = cond_br %110#1, %result_58 {handshake.bb = 8 : ui32, handshake.name = "cond_br35"} : <i1>, <>
    %trueResult_66, %falseResult_67 = cond_br %110#0, %106#0 {handshake.bb = 8 : ui32, handshake.name = "cond_br36"} : <i1>, <i32>
    sink %trueResult_66 {handshake.name = "sink10"} : <i32>
    %111 = merge %trueResult_82 {handshake.bb = 9 : ui32, handshake.name = "merge10"} : <i32>
    %112:2 = fork [2] %111 {handshake.bb = 9 : ui32, handshake.name = "fork28"} : <i32>
    %113 = merge %trueResult_84 {handshake.bb = 9 : ui32, handshake.name = "merge11"} : <i32>
    %114 = merge %trueResult_86 {handshake.bb = 9 : ui32, handshake.name = "merge12"} : <i32>
    %115:2 = fork [2] %114 {handshake.bb = 9 : ui32, handshake.name = "fork29"} : <i32>
    %116 = merge %trueResult_88 {handshake.bb = 9 : ui32, handshake.name = "merge13"} : <i32>
    %117:2 = fork [2] %116 {handshake.bb = 9 : ui32, handshake.name = "fork30"} : <i32>
    %result_68, %index_69 = control_merge [%trueResult_90]  {handshake.bb = 9 : ui32, handshake.name = "control_merge8"} : [<>] to <>, <i1>
    sink %index_69 {handshake.name = "sink11"} : <i1>
    %118 = source {handshake.bb = 9 : ui32, handshake.name = "source10"} : <>
    %119 = constant %118 {handshake.bb = 9 : ui32, handshake.name = "constant13", value = 0 : i32} : <>, <i32>
    %120 = cmpi slt, %115#1, %117#1 {handshake.bb = 9 : ui32, handshake.name = "cmpi9"} : <i32>
    %121 = select %120[%115#0, %117#0] {handshake.bb = 9 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %122 = cmpi eq, %112#1, %119 {handshake.bb = 9 : ui32, handshake.name = "cmpi10"} : <i32>
    %123:4 = fork [4] %122 {handshake.bb = 9 : ui32, handshake.name = "fork31"} : <i1>
    %trueResult_70, %falseResult_71 = cond_br %123#3, %121 {handshake.bb = 9 : ui32, handshake.name = "cond_br37"} : <i1>, <i32>
    %trueResult_72, %falseResult_73 = cond_br %123#2, %113 {handshake.bb = 9 : ui32, handshake.name = "cond_br38"} : <i1>, <i32>
    %trueResult_74, %falseResult_75 = cond_br %123#1, %result_68 {handshake.bb = 9 : ui32, handshake.name = "cond_br39"} : <i1>, <>
    %trueResult_76, %falseResult_77 = cond_br %123#0, %112#0 {handshake.bb = 9 : ui32, handshake.name = "cond_br40"} : <i1>, <i32>
    sink %trueResult_76 {handshake.name = "sink12"} : <i32>
    %124 = mux %129#0 [%falseResult_67, %falseResult_77] {handshake.bb = 10 : ui32, handshake.name = "mux12"} : <i1>, [<i32>, <i32>] to <i32>
    %125:2 = fork [2] %124 {handshake.bb = 10 : ui32, handshake.name = "fork32"} : <i32>
    %126 = mux %129#1 [%falseResult_61, %falseResult_71] {handshake.bb = 10 : ui32, handshake.name = "mux13"} : <i1>, [<i32>, <i32>] to <i32>
    %127:2 = fork [2] %126 {handshake.bb = 10 : ui32, handshake.name = "fork33"} : <i32>
    %128 = mux %129#2 [%falseResult_63, %falseResult_73] {handshake.bb = 10 : ui32, handshake.name = "mux14"} : <i1>, [<i32>, <i32>] to <i32>
    %result_78, %index_79 = control_merge [%falseResult_65, %falseResult_75]  {handshake.bb = 10 : ui32, handshake.name = "control_merge9"} : [<>, <>] to <>, <i1>
    %129:3 = fork [3] %index_79 {handshake.bb = 10 : ui32, handshake.name = "fork34"} : <i1>
    %130 = source {handshake.bb = 10 : ui32, handshake.name = "source11"} : <>
    %131 = constant %130 {handshake.bb = 10 : ui32, handshake.name = "constant14", value = -1 : i32} : <>, <i32>
    %132 = source {handshake.bb = 10 : ui32, handshake.name = "source12"} : <>
    %133 = constant %132 {handshake.bb = 10 : ui32, handshake.name = "constant15", value = 0 : i32} : <>, <i32>
    %134 = subi %127#1, %125#1 {handshake.bb = 10 : ui32, handshake.name = "subi0"} : <i32>
    %135:3 = fork [3] %134 {handshake.bb = 10 : ui32, handshake.name = "fork35"} : <i32>
    %136 = cmpi sgt, %135#2, %131 {handshake.bb = 10 : ui32, handshake.name = "cmpi11"} : <i32>
    %137 = subi %133, %135#1 {handshake.bb = 10 : ui32, handshake.name = "subi1"} : <i32>
    %138 = select %136[%135#0, %137] {handshake.bb = 10 : ui32, handshake.name = "select1"} : <i1>, <i32>
    %139 = br %138 {handshake.bb = 10 : ui32, handshake.name = "br12"} : <i32>
    %140 = br %128 {handshake.bb = 10 : ui32, handshake.name = "br13"} : <i32>
    %141 = br %125#0 {handshake.bb = 10 : ui32, handshake.name = "br14"} : <i32>
    %142 = br %127#0 {handshake.bb = 10 : ui32, handshake.name = "br15"} : <i32>
    %143 = br %result_78 {handshake.bb = 10 : ui32, handshake.name = "br16"} : <>
    %144 = mux %151#0 [%139, %falseResult_93] {handshake.bb = 11 : ui32, handshake.name = "mux15"} : <i1>, [<i32>, <i32>] to <i32>
    %145:4 = fork [4] %144 {handshake.bb = 11 : ui32, handshake.name = "fork36"} : <i32>
    %146 = trunci %145#0 {handshake.bb = 11 : ui32, handshake.name = "trunci4"} : <i32> to <i1>
    %147 = constant %153#0 {handshake.bb = 11 : ui32, handshake.name = "constant25", value = true} : <>, <i1>
    %148 = mux %151#1 [%140, %falseResult_85] {handshake.bb = 11 : ui32, handshake.name = "mux16"} : <i1>, [<i32>, <i32>] to <i32>
    %149 = mux %151#2 [%141, %falseResult_87] {handshake.bb = 11 : ui32, handshake.name = "mux17"} : <i1>, [<i32>, <i32>] to <i32>
    %150 = mux %151#3 [%142, %falseResult_89] {handshake.bb = 11 : ui32, handshake.name = "mux18"} : <i1>, [<i32>, <i32>] to <i32>
    %result_80, %index_81 = control_merge [%143, %falseResult_91]  {handshake.bb = 11 : ui32, handshake.name = "control_merge10"} : [<>, <>] to <>, <i1>
    %151:4 = fork [4] %index_81 {handshake.bb = 11 : ui32, handshake.name = "fork37"} : <i1>
    %152 = source {handshake.bb = 11 : ui32, handshake.name = "source13"} : <>
    %153:2 = fork [2] %152 {handshake.bb = 11 : ui32, handshake.name = "fork38"} : <>
    %154 = constant %153#1 {handshake.bb = 11 : ui32, handshake.name = "constant16", value = 1 : i32} : <>, <i32>
    %155:2 = fork [2] %154 {handshake.bb = 11 : ui32, handshake.name = "fork39"} : <i32>
    %156 = source {handshake.bb = 11 : ui32, handshake.name = "source14"} : <>
    %157 = cmpi slt, %145#3, %155#1 {handshake.bb = 11 : ui32, handshake.name = "cmpi12"} : <i32>
    %158 = andi %146, %147 {handshake.bb = 11 : ui32, handshake.name = "andi4"} : <i1>
    %159 = constant %156 {handshake.bb = 11 : ui32, handshake.name = "constant26", value = false} : <>, <i1>
    %160 = cmpi ne, %158, %159 {handshake.bb = 11 : ui32, handshake.name = "cmpi13"} : <i1>
    %161 = ori %160, %157 {handshake.bb = 11 : ui32, handshake.name = "ori4"} : <i1>
    %162:6 = fork [6] %161 {handshake.bb = 11 : ui32, handshake.name = "fork40"} : <i1>
    %163 = shrsi %145#2, %155#0 {handshake.bb = 11 : ui32, handshake.name = "shrsi4"} : <i32>
    %trueResult_82, %falseResult_83 = cond_br %162#5, %145#1 {handshake.bb = 11 : ui32, handshake.name = "cond_br41"} : <i1>, <i32>
    sink %falseResult_83 {handshake.name = "sink13"} : <i32>
    %trueResult_84, %falseResult_85 = cond_br %162#4, %148 {handshake.bb = 11 : ui32, handshake.name = "cond_br42"} : <i1>, <i32>
    %trueResult_86, %falseResult_87 = cond_br %162#3, %149 {handshake.bb = 11 : ui32, handshake.name = "cond_br43"} : <i1>, <i32>
    %trueResult_88, %falseResult_89 = cond_br %162#2, %150 {handshake.bb = 11 : ui32, handshake.name = "cond_br44"} : <i1>, <i32>
    %trueResult_90, %falseResult_91 = cond_br %162#1, %result_80 {handshake.bb = 11 : ui32, handshake.name = "cond_br45"} : <i1>, <>
    %trueResult_92, %falseResult_93 = cond_br %162#0, %163 {handshake.bb = 11 : ui32, handshake.name = "cond_br46"} : <i1>, <i32>
    sink %trueResult_92 {handshake.name = "sink14"} : <i32>
    %164 = mux %166#0 [%trueResult_60, %trueResult_70] {handshake.bb = 12 : ui32, handshake.name = "mux19"} : <i1>, [<i32>, <i32>] to <i32>
    %165 = mux %166#1 [%trueResult_62, %trueResult_72] {handshake.bb = 12 : ui32, handshake.name = "mux20"} : <i1>, [<i32>, <i32>] to <i32>
    %result_94, %index_95 = control_merge [%trueResult_64, %trueResult_74]  {handshake.bb = 12 : ui32, handshake.name = "control_merge11"} : [<>, <>] to <>, <i1>
    %166:2 = fork [2] %index_95 {handshake.bb = 12 : ui32, handshake.name = "fork41"} : <i1>
    %167 = shli %164, %165 {handshake.bb = 12 : ui32, handshake.name = "shli0"} : <i32>
    %168 = br %167 {handshake.bb = 12 : ui32, handshake.name = "br17"} : <i32>
    %169 = br %result_94 {handshake.bb = 12 : ui32, handshake.name = "br18"} : <>
    %170 = mux %index_97 [%trueResult, %trueResult_4, %168] {handshake.bb = 13 : ui32, handshake.name = "mux21"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %result_96, %index_97 = control_merge [%trueResult_0, %trueResult_6, %169]  {handshake.bb = 13 : ui32, handshake.name = "control_merge12"} : [<>, <>, <>] to <>, <i2>
    sink %result_96 {handshake.name = "sink15"} : <>
    end {handshake.bb = 13 : ui32, handshake.name = "end0"} %170, %0#0 : <i32>, <>
  }
}

