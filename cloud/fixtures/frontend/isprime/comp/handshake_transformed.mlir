module {
  handshake.func @isprime(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["n", "start"], resNames = ["out0", "end"]} {
    %0:3 = fork [3] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg0 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %3 = constant %2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 2 : i32} : <>, <i32>
    %4 = cmpi slt, %1#1, %3 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %5:3 = fork [3] %4 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %6 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %5#0, %6 {handshake.bb = 0 : ui32, handshake.name = "cond_br7"} : <i1>, <i1>
    sink %falseResult {handshake.name = "sink0"} : <i1>
    %trueResult_0, %falseResult_1 = cond_br %5#2, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %5#1, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    sink %trueResult_2 {handshake.name = "sink1"} : <i32>
    %7 = merge %falseResult_3 {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %8:2 = fork [2] %7 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %result, %index = control_merge [%falseResult_1]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    sink %index {handshake.name = "sink2"} : <i1>
    %9:3 = fork [3] %result {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <>
    %10 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %11 = constant %10 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 4 : i32} : <>, <i32>
    %12 = cmpi slt, %8#1, %11 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %13:4 = fork [4] %12 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i1>
    %14 = constant %9#0 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = true} : <>, <i1>
    %trueResult_4, %falseResult_5 = cond_br %13#0, %14 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i1>
    sink %falseResult_5 {handshake.name = "sink3"} : <i1>
    %trueResult_6, %falseResult_7 = cond_br %13#3, %9#2 {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %15 = constant %9#1 {handshake.bb = 1 : ui32, handshake.name = "constant13", value = -2 : i2} : <>, <i2>
    %trueResult_8, %falseResult_9 = cond_br %13#1, %15 {handshake.bb = 1 : ui32, handshake.name = "cond_br12"} : <i1>, <i2>
    sink %trueResult_8 {handshake.name = "sink4"} : <i2>
    %16 = extui %falseResult_9 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i2> to <i32>
    %trueResult_10, %falseResult_11 = cond_br %13#2, %8#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    sink %trueResult_10 {handshake.name = "sink5"} : <i32>
    %17 = merge %falseResult_67 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %18:3 = fork [3] %17 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i32>
    %19 = merge %falseResult_69 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %20:2 = fork [2] %19 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i32>
    %result_12, %index_13 = control_merge [%falseResult_65]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_13 {handshake.name = "sink6"} : <i1>
    %21:2 = fork [2] %result_12 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <>
    %22 = muli %18#1, %18#2 {handshake.bb = 2 : ui32, handshake.name = "muli0"} : <i32>
    %23 = cmpi sgt, %22, %20#1 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i32>
    %24:4 = fork [4] %23 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i1>
    %25 = constant %21#0 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = true} : <>, <i1>
    %trueResult_14, %falseResult_15 = cond_br %24#0, %25 {handshake.bb = 2 : ui32, handshake.name = "cond_br14"} : <i1>, <i1>
    sink %falseResult_15 {handshake.name = "sink7"} : <i1>
    %trueResult_16, %falseResult_17 = cond_br %24#3, %21#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %trueResult_18, %falseResult_19 = cond_br %24#2, %18#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    sink %trueResult_18 {handshake.name = "sink8"} : <i32>
    %trueResult_20, %falseResult_21 = cond_br %24#1, %20#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    sink %trueResult_20 {handshake.name = "sink9"} : <i32>
    %26 = mux %29#0 [%16, %falseResult_19] {handshake.bb = 3 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %27 = mux %29#1 [%falseResult_11, %falseResult_21] {handshake.bb = 3 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %28:2 = fork [2] %27 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i32>
    %result_22, %index_23 = control_merge [%falseResult_7, %falseResult_17]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %29:2 = fork [2] %index_23 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i1>
    %30 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %31 = constant %30 {handshake.bb = 3 : ui32, handshake.name = "constant8", value = 1 : i32} : <>, <i32>
    %32 = shrsi %28#1, %31 {handshake.bb = 3 : ui32, handshake.name = "shrsi0"} : <i32>
    %33 = br %26 {handshake.bb = 3 : ui32, handshake.name = "br1"} : <i32>
    %34:2 = fork [2] %33 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <i32>
    %35 = br %28#0 {handshake.bb = 3 : ui32, handshake.name = "br2"} : <i32>
    %36 = br %32 {handshake.bb = 3 : ui32, handshake.name = "br3"} : <i32>
    %37 = br %result_22 {handshake.bb = 3 : ui32, handshake.name = "br4"} : <>
    %38 = mux %44#0 [%34#1, %falseResult_35] {handshake.bb = 4 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %39:3 = fork [3] %38 {handshake.bb = 4 : ui32, handshake.name = "fork13"} : <i32>
    %40 = mux %44#1 [%35, %falseResult_29] {handshake.bb = 4 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %41 = mux %44#2 [%34#0, %falseResult_31] {handshake.bb = 4 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %42 = mux %44#3 [%36, %falseResult_37] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %43:2 = fork [2] %42 {handshake.bb = 4 : ui32, handshake.name = "fork14"} : <i32>
    %result_24, %index_25 = control_merge [%37, %falseResult_33]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %44:4 = fork [4] %index_25 {handshake.bb = 4 : ui32, handshake.name = "fork15"} : <i1>
    %45 = source {handshake.bb = 4 : ui32, handshake.name = "source3"} : <>
    %46 = constant %45 {handshake.bb = 4 : ui32, handshake.name = "constant9", value = 1 : i32} : <>, <i32>
    %47 = cmpi sgt, %39#2, %43#1 {handshake.bb = 4 : ui32, handshake.name = "cmpi3"} : <i32>
    %48:6 = fork [6] %47 {handshake.bb = 4 : ui32, handshake.name = "fork16"} : <i1>
    %49 = shli %39#1, %46 {handshake.bb = 4 : ui32, handshake.name = "shli0"} : <i32>
    %trueResult_26, %falseResult_27 = cond_br %48#5, %39#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    sink %falseResult_27 {handshake.name = "sink10"} : <i32>
    %trueResult_28, %falseResult_29 = cond_br %48#4, %40 {handshake.bb = 4 : ui32, handshake.name = "cond_br19"} : <i1>, <i32>
    %trueResult_30, %falseResult_31 = cond_br %48#3, %41 {handshake.bb = 4 : ui32, handshake.name = "cond_br20"} : <i1>, <i32>
    %trueResult_32, %falseResult_33 = cond_br %48#2, %result_24 {handshake.bb = 4 : ui32, handshake.name = "cond_br21"} : <i1>, <>
    %trueResult_34, %falseResult_35 = cond_br %48#1, %49 {handshake.bb = 4 : ui32, handshake.name = "cond_br22"} : <i1>, <i32>
    sink %trueResult_34 {handshake.name = "sink11"} : <i32>
    %trueResult_36, %falseResult_37 = cond_br %48#0, %43#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br23"} : <i1>, <i32>
    sink %trueResult_36 {handshake.name = "sink12"} : <i32>
    %50 = merge %trueResult_26 {handshake.bb = 5 : ui32, handshake.name = "merge3"} : <i32>
    %51:2 = fork [2] %50 {handshake.bb = 5 : ui32, handshake.name = "fork17"} : <i32>
    %52 = merge %trueResult_28 {handshake.bb = 5 : ui32, handshake.name = "merge4"} : <i32>
    %53 = merge %trueResult_30 {handshake.bb = 5 : ui32, handshake.name = "merge5"} : <i32>
    %54:2 = fork [2] %53 {handshake.bb = 5 : ui32, handshake.name = "fork18"} : <i32>
    %result_38, %index_39 = control_merge [%trueResult_32]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    sink %index_39 {handshake.name = "sink13"} : <i1>
    %55 = cmpi slt, %51#1, %54#1 {handshake.bb = 5 : ui32, handshake.name = "cmpi4"} : <i32>
    %56:4 = fork [4] %55 {handshake.bb = 5 : ui32, handshake.name = "fork19"} : <i1>
    %trueResult_40, %falseResult_41 = cond_br %56#3, %52 {handshake.bb = 5 : ui32, handshake.name = "cond_br24"} : <i1>, <i32>
    %57:2 = fork [2] %falseResult_41 {handshake.bb = 5 : ui32, handshake.name = "fork20"} : <i32>
    %58:2 = fork [2] %trueResult_40 {handshake.bb = 5 : ui32, handshake.name = "fork21"} : <i32>
    %trueResult_42, %falseResult_43 = cond_br %56#2, %54#0 {handshake.bb = 5 : ui32, handshake.name = "cond_br25"} : <i1>, <i32>
    %trueResult_44, %falseResult_45 = cond_br %56#1, %result_38 {handshake.bb = 5 : ui32, handshake.name = "cond_br26"} : <i1>, <>
    %trueResult_46, %falseResult_47 = cond_br %56#0, %51#0 {handshake.bb = 5 : ui32, handshake.name = "cond_br27"} : <i1>, <i32>
    sink %trueResult_46 {handshake.name = "sink14"} : <i32>
    %59 = mux %66#0 [%falseResult_47, %falseResult_59] {handshake.bb = 6 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %60:3 = fork [3] %59 {handshake.bb = 6 : ui32, handshake.name = "fork22"} : <i32>
    %61 = mux %66#1 [%57#1, %falseResult_51] {handshake.bb = 6 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %62:3 = fork [3] %61 {handshake.bb = 6 : ui32, handshake.name = "fork23"} : <i32>
    %63 = mux %66#2 [%57#0, %falseResult_53] {handshake.bb = 6 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %64 = mux %66#3 [%falseResult_43, %falseResult_55] {handshake.bb = 6 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %65:2 = fork [2] %64 {handshake.bb = 6 : ui32, handshake.name = "fork24"} : <i32>
    %result_48, %index_49 = control_merge [%falseResult_45, %falseResult_57]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>, <>] to <>, <i1>
    %66:4 = fork [4] %index_49 {handshake.bb = 6 : ui32, handshake.name = "fork25"} : <i1>
    %67 = source {handshake.bb = 6 : ui32, handshake.name = "source4"} : <>
    %68 = constant %67 {handshake.bb = 6 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %69 = cmpi slt, %62#2, %60#2 {handshake.bb = 6 : ui32, handshake.name = "cmpi5"} : <i32>
    %70 = subi %62#1, %60#1 {handshake.bb = 6 : ui32, handshake.name = "subi0"} : <i32>
    %71 = select %69[%62#0, %70] {handshake.bb = 6 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %72 = shrsi %60#0, %68 {handshake.bb = 6 : ui32, handshake.name = "shrsi1"} : <i32>
    %73:2 = fork [2] %72 {handshake.bb = 6 : ui32, handshake.name = "fork26"} : <i32>
    %74 = cmpi slt, %73#1, %65#1 {handshake.bb = 6 : ui32, handshake.name = "cmpi6"} : <i32>
    %75:5 = fork [5] %74 {handshake.bb = 6 : ui32, handshake.name = "fork27"} : <i1>
    %trueResult_50, %falseResult_51 = cond_br %75#4, %71 {handshake.bb = 6 : ui32, handshake.name = "cond_br28"} : <i1>, <i32>
    %trueResult_52, %falseResult_53 = cond_br %75#3, %63 {handshake.bb = 6 : ui32, handshake.name = "cond_br29"} : <i1>, <i32>
    %trueResult_54, %falseResult_55 = cond_br %75#2, %65#0 {handshake.bb = 6 : ui32, handshake.name = "cond_br30"} : <i1>, <i32>
    %trueResult_56, %falseResult_57 = cond_br %75#1, %result_48 {handshake.bb = 6 : ui32, handshake.name = "cond_br31"} : <i1>, <>
    %trueResult_58, %falseResult_59 = cond_br %75#0, %73#0 {handshake.bb = 6 : ui32, handshake.name = "cond_br32"} : <i1>, <i32>
    sink %trueResult_58 {handshake.name = "sink15"} : <i32>
    %76 = mux %79#0 [%58#1, %trueResult_50] {handshake.bb = 7 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %77 = mux %79#1 [%58#0, %trueResult_52] {handshake.bb = 7 : ui32, handshake.name = "mux11"} : <i1>, [<i32>, <i32>] to <i32>
    %78 = mux %79#2 [%trueResult_42, %trueResult_54] {handshake.bb = 7 : ui32, handshake.name = "mux12"} : <i1>, [<i32>, <i32>] to <i32>
    %result_60, %index_61 = control_merge [%trueResult_44, %trueResult_56]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>, <>] to <>, <i1>
    %79:3 = fork [3] %index_61 {handshake.bb = 7 : ui32, handshake.name = "fork28"} : <i1>
    %80:3 = fork [3] %result_60 {handshake.bb = 7 : ui32, handshake.name = "fork29"} : <>
    %81 = constant %80#2 {handshake.bb = 7 : ui32, handshake.name = "constant11", value = 0 : i32} : <>, <i32>
    %82 = source {handshake.bb = 7 : ui32, handshake.name = "source5"} : <>
    %83 = constant %82 {handshake.bb = 7 : ui32, handshake.name = "constant12", value = 1 : i32} : <>, <i32>
    %84 = cmpi eq, %76, %81 {handshake.bb = 7 : ui32, handshake.name = "cmpi7"} : <i32>
    %85:4 = fork [4] %84 {handshake.bb = 7 : ui32, handshake.name = "fork30"} : <i1>
    %86 = addi %78, %83 {handshake.bb = 7 : ui32, handshake.name = "addi0"} : <i32>
    %87 = constant %80#0 {handshake.bb = 7 : ui32, handshake.name = "constant15", value = false} : <>, <i1>
    %trueResult_62, %falseResult_63 = cond_br %85#0, %87 {handshake.bb = 7 : ui32, handshake.name = "cond_br33"} : <i1>, <i1>
    sink %falseResult_63 {handshake.name = "sink16"} : <i1>
    %trueResult_64, %falseResult_65 = cond_br %85#3, %80#1 {handshake.bb = 7 : ui32, handshake.name = "cond_br34"} : <i1>, <>
    %trueResult_66, %falseResult_67 = cond_br %85#2, %86 {handshake.bb = 7 : ui32, handshake.name = "cond_br35"} : <i1>, <i32>
    sink %trueResult_66 {handshake.name = "sink17"} : <i32>
    %trueResult_68, %falseResult_69 = cond_br %85#1, %77 {handshake.bb = 7 : ui32, handshake.name = "cond_br36"} : <i1>, <i32>
    sink %trueResult_68 {handshake.name = "sink18"} : <i32>
    %88 = mux %index_71 [%trueResult, %trueResult_4, %trueResult_14, %trueResult_62] {handshake.bb = 8 : ui32, handshake.name = "mux13"} : <i2>, [<i1>, <i1>, <i1>, <i1>] to <i1>
    %89 = extui %88 {handshake.bb = 8 : ui32, handshake.name = "extui1"} : <i1> to <i32>
    %result_70, %index_71 = control_merge [%trueResult_0, %trueResult_6, %trueResult_16, %trueResult_64]  {handshake.bb = 8 : ui32, handshake.name = "control_merge7"} : [<>, <>, <>, <>] to <>, <i2>
    sink %result_70 {handshake.name = "sink19"} : <>
    end {handshake.bb = 8 : ui32, handshake.name = "end0"} %89, %0#1 : <i32>, <>
  }
}

