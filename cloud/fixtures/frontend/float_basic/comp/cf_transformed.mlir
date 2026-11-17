module {
  func.func @float_basic(%arg0: memref<900xf32> {handshake.arg_name = "A"}, %arg1: memref<900xf32> {handshake.arg_name = "B"}, %arg2: memref<30xf32> {handshake.arg_name = "y"}, %arg3: memref<30xf32> {handshake.arg_name = "x"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb6
    %cst = arith.constant {handshake.name = "constant9"} 0.000000e+00 : f32
    %c0_i32_0 = arith.constant {handshake.name = "constant10"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    cf.br ^bb2(%cst, %c0_i32_0 : f32, i32) {handshake.name = "br1"}
  ^bb2(%3: f32, %4: i32):  // 2 preds: ^bb1, ^bb5
    %c4_i64 = arith.constant {handshake.name = "constant11"} 4 : i64
    %c3_i64 = arith.constant {handshake.name = "constant12"} 3 : i64
    %c2_i64 = arith.constant {handshake.name = "constant13"} 2 : i64
    %c1_i64 = arith.constant {handshake.name = "constant14"} 1 : i64
    %5 = arith.extui %4 {handshake.name = "extui2"} : i32 to i64
    %6 = arith.index_cast %5 {handshake.name = "index_cast0"} : i64 to index
    %7 = memref.load %arg3[%6] {handshake.name = "load0"} : memref<30xf32>
    %8 = arith.extui %4 {handshake.name = "extui3"} : i32 to i64
    %9 = arith.shli %1, %c1_i64 {handshake.name = "shli0"} : i64
    %10 = arith.shli %1, %c2_i64 {handshake.name = "shli1"} : i64
    %11 = arith.addi %9, %10 {handshake.name = "addi6"} : i64
    %12 = arith.shli %1, %c3_i64 {handshake.name = "shli2"} : i64
    %13 = arith.shli %1, %c4_i64 {handshake.name = "shli3"} : i64
    %14 = arith.addi %12, %13 {handshake.name = "addi7"} : i64
    %15 = arith.addi %11, %14 {handshake.name = "addi8"} : i64
    %16 = arith.addi %15, %8 {handshake.name = "addi0"} : i64
    %17 = arith.index_cast %16 {handshake.name = "index_cast1"} : i64 to index
    %18 = memref.load %arg0[%17] {handshake.name = "load1"} : memref<900xf32>
    %19 = arith.extui %4 {handshake.name = "extui4"} : i32 to i64
    %20 = arith.shli %2, %c1_i64 {handshake.name = "shli4"} : i64
    %21 = arith.shli %2, %c2_i64 {handshake.name = "shli5"} : i64
    %22 = arith.addi %20, %21 {handshake.name = "addi9"} : i64
    %23 = arith.shli %2, %c3_i64 {handshake.name = "shli6"} : i64
    %24 = arith.shli %2, %c4_i64 {handshake.name = "shli7"} : i64
    %25 = arith.addi %23, %24 {handshake.name = "addi10"} : i64
    %26 = arith.addi %22, %25 {handshake.name = "addi11"} : i64
    %27 = arith.addi %26, %19 {handshake.name = "addi1"} : i64
    %28 = arith.index_cast %27 {handshake.name = "index_cast2"} : i64 to index
    %29 = memref.load %arg1[%28] {handshake.name = "load2"} : memref<900xf32>
    %30 = arith.cmpf ugt, %18, %29 {handshake.name = "cmpf0"} : f32
    cf.cond_br %30, ^bb4, ^bb3 {handshake.name = "cond_br0"}
  ^bb3:  // pred: ^bb2
    %c4_i64_1 = arith.constant {handshake.name = "constant15"} 4 : i64
    %c3_i64_2 = arith.constant {handshake.name = "constant16"} 3 : i64
    %c2_i64_3 = arith.constant {handshake.name = "constant17"} 2 : i64
    %c1_i64_4 = arith.constant {handshake.name = "constant18"} 1 : i64
    %31 = arith.extui %0 {handshake.name = "extui5"} : i32 to i64
    %32 = arith.extui %4 {handshake.name = "extui6"} : i32 to i64
    %33 = arith.shli %31, %c1_i64_4 {handshake.name = "shli8"} : i64
    %34 = arith.shli %31, %c2_i64_3 {handshake.name = "shli9"} : i64
    %35 = arith.addi %33, %34 {handshake.name = "addi12"} : i64
    %36 = arith.shli %31, %c3_i64_2 {handshake.name = "shli10"} : i64
    %37 = arith.shli %31, %c4_i64_1 {handshake.name = "shli11"} : i64
    %38 = arith.addi %36, %37 {handshake.name = "addi13"} : i64
    %39 = arith.addi %35, %38 {handshake.name = "addi14"} : i64
    %40 = arith.addi %39, %32 {handshake.name = "addi2"} : i64
    %41 = arith.index_cast %40 {handshake.name = "index_cast3"} : i64 to index
    %42 = memref.load %arg0[%41] {handshake.name = "load3"} : memref<900xf32>
    %43 = arith.divf %42, %7 {handshake.name = "divf0"} : f32
    %44 = arith.addf %3, %43 {handshake.name = "addf0"} : f32
    cf.br ^bb5(%44 : f32) {handshake.name = "br2"}
  ^bb4:  // pred: ^bb2
    %c4_i64_5 = arith.constant {handshake.name = "constant19"} 4 : i64
    %c3_i64_6 = arith.constant {handshake.name = "constant20"} 3 : i64
    %c2_i64_7 = arith.constant {handshake.name = "constant21"} 2 : i64
    %c1_i64_8 = arith.constant {handshake.name = "constant22"} 1 : i64
    %45 = arith.extui %0 {handshake.name = "extui7"} : i32 to i64
    %46 = arith.extui %4 {handshake.name = "extui8"} : i32 to i64
    %47 = arith.shli %45, %c1_i64_8 {handshake.name = "shli12"} : i64
    %48 = arith.shli %45, %c2_i64_7 {handshake.name = "shli13"} : i64
    %49 = arith.addi %47, %48 {handshake.name = "addi15"} : i64
    %50 = arith.shli %45, %c3_i64_6 {handshake.name = "shli14"} : i64
    %51 = arith.shli %45, %c4_i64_5 {handshake.name = "shli15"} : i64
    %52 = arith.addi %50, %51 {handshake.name = "addi16"} : i64
    %53 = arith.addi %49, %52 {handshake.name = "addi17"} : i64
    %54 = arith.addi %53, %46 {handshake.name = "addi3"} : i64
    %55 = arith.index_cast %54 {handshake.name = "index_cast4"} : i64 to index
    %56 = memref.load %arg1[%55] {handshake.name = "load4"} : memref<900xf32>
    %57 = arith.mulf %56, %7 {handshake.name = "mulf0"} : f32
    %58 = arith.subf %3, %57 {handshake.name = "subf0"} : f32
    cf.br ^bb5(%58 : f32) {handshake.name = "br3"}
  ^bb5(%59: f32):  // 2 preds: ^bb3, ^bb4
    %c30_i32 = arith.constant {handshake.name = "constant23"} 30 : i32
    %c1_i32 = arith.constant {handshake.name = "constant24"} 1 : i32
    %60 = arith.addi %4, %c1_i32 {handshake.name = "addi4"} : i32
    %61 = arith.cmpi ult, %60, %c30_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %61, ^bb2(%59, %60 : f32, i32), ^bb6(%59 : f32) {handshake.name = "cond_br1"}
  ^bb6(%62: f32):  // pred: ^bb5
    %c30_i32_9 = arith.constant {handshake.name = "constant25"} 30 : i32
    %c1_i32_10 = arith.constant {handshake.name = "constant26"} 1 : i32
    %63 = arith.extui %0 {handshake.name = "extui9"} : i32 to i64
    %64 = arith.index_cast %63 {handshake.name = "index_cast5"} : i64 to index
    memref.store %62, %arg2[%64] {handshake.name = "store5"} : memref<30xf32>
    %65 = arith.addi %0, %c1_i32_10 {handshake.name = "addi5"} : i32
    %66 = arith.cmpi ult, %65, %c30_i32_9 {handshake.name = "cmpi1"} : i32
    cf.cond_br %66, ^bb1(%65 : i32), ^bb7 {handshake.name = "cond_br2"}
  ^bb7:  // pred: ^bb6
    return {handshake.name = "return0"}
  }
}

