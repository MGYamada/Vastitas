mod common;
use common::{Scratch, cli, kernel, success};
use serde_json::{Value, json};
use std::os::unix::fs::PermissionsExt;
use std::process::Command;

const REAL: &str = include_str!("../examples/packages/contraction-tree/src/real/mod.vast");
const COMPLEX: &str = include_str!("../examples/packages/contraction-tree/src/complex/mod.vast");

fn fixture(real: &str, complex: &str) -> Scratch {
    let s = Scratch::empty("contraction tree");
    s.write(
        "Vastitas.toml",
        include_str!("../examples/packages/contraction-tree/Vastitas.toml"),
    );
    s.write(
        "src/main.vast",
        include_str!("../examples/packages/contraction-tree/src/main.vast"),
    );
    s.write(
        "src/profiles/mod.vast",
        include_str!("../examples/packages/contraction-tree/src/profiles/mod.vast"),
    );
    s.write("src/real/mod.vast", real);
    s.write("src/complex/mod.vast", complex);
    s
}
fn command(s: &Scratch, mode: &str) -> Command {
    let mut command = cli();
    command
        .current_dir(&s.0)
        .args([mode, "--manifest-path", "Vastitas.toml"]);
    command
}
fn captured(s: &Scratch) -> Value {
    let stub = s.write("capture", "#!/bin/sh\ncat > \"$(dirname \"$0\")/wire.json\"\nprintf '%s\\n' '{\"version\":8,\"ok\":false,\"diagnostics\":[{\"code\":\"E_CAPTURED\",\"message\":\"captured\"}]}'\nexit 1\n");
    std::fs::set_permissions(&stub, std::fs::Permissions::from_mode(0o755)).unwrap();
    let output = command(s, "check")
        .env("VASTITAS_KERNEL", stub)
        .output()
        .unwrap();
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("E_CAPTURED"),
        "{output:?}"
    );
    serde_json::from_slice(&std::fs::read(s.0.join("wire.json")).unwrap()).unwrap()
}

fn wire_rejected(raw: Value) {
    let response = kernel(raw, "emit");
    assert_eq!(response["ok"], false, "{response}");
    assert!(response.get("lean_source").is_none());
}
fn tree(raw: &mut Value) -> &mut Value {
    raw["packages"][0]["modules"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|module| module["path"] == json!(["real"]))
        .unwrap()["resource_functions"][0]["body"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|statement| statement["kind"] == "tree")
        .unwrap()
}
fn rejection(source: &str, code: &str) {
    let result = command(&fixture(source, COMPLEX), "check")
        .output()
        .unwrap();
    assert!(!result.status.success(), "accepted invalid tree: {source}");
    assert!(
        String::from_utf8_lossy(&result.stderr).contains(code),
        "{result:?}"
    );
}
fn branched(source: &str, condition: bool) -> String {
    let start = source.find("    contract_tree").unwrap();
    let end = source.find("    release(output);").unwrap();
    let block = &source[start..end];
    format!(
        "{} if {condition} {{ {block} }} else {{ {block} }} {}",
        &source[..start],
        &source[end..]
    )
}

// Four occurrences and three edges, with an actual rank-two × rank-three
// first contraction in the opposite orientation from the two-edge fixture.
// The diagonal D scales T's free coordinate by 2 and 3 respectively; all
// following coordinate assertions are independently rescaled accordingly.
fn four_occurrences(source: &str, complex: bool) -> String {
    let scalar = if complex { "Complex<F64>" } else { "F64" };
    let profile = if complex {
        "ComplexSmooth"
    } else {
        "RealSmooth"
    };
    let width = if complex { 16 } else { 8 };
    let bits = |n: f64| {
        if complex {
            format!("complex_bits({}, 0)", n.to_bits())
        } else {
            format!("f64_bits({})", n.to_bits())
        }
    };
    let source = source.replace("    allocate original:", &format!(
        "    space z = linear(super::profiles::{profile}, 2); basis bz = basis(z);\n    space ud = dual(u); basis bud = derived(bu, ud);\n    allocate diagonal: {scalar}[9]; allocate first_result: {scalar}[39];\n    borrow init_d = write(diagonal, layout({width}, 2, 2, 3, false));\n    fill(init_d, {}); store(init_d, 0, 0, {}); store(init_d, 1, 1, {}); release(init_d);\n    borrow input_d = read(diagonal, layout({width}, 2, 2, 3, false)); tensor left_d = view2(input_d, bz, bud);\n    allocate original:", bits(0.0), bits(2.0), bits(3.0)));
    let source = source.replace("tensor c = view3(output, bu", "tensor c = view3(output, bz")
        .replace("occurrence t = t;", "occurrence t = t; occurrence d = left_d;")
        .replace("edge ev =", "edge eu = (d[1], t[0]); edge ev =")
        .replace("boundary(t[0]", "boundary(d[0]")
        .replace("plan {", &format!("plan {{\n    borrow dt_write = write(first_result, layout({width}, 2, 12, 3, false));\n    tensor dt_output = view3(dt_write, bz, bvd, bwd, axes(0,1,2), 1);\n    join dt = (eu, d, t, dt_output); release(dt_write);\n    borrow dt_read = read(first_result, layout({width}, 2, 12, 3, false));\n    tensor dt_input = view3(dt_read, bz, bvd, bwd, axes(0,1,2), 1); rebind(dt, dt_input);"))
        .replace("view3(packed_write, bu", "view3(packed_write, bz")
        .replace("view3(packed_read, bu", "view3(packed_read, bz")
        .replace("view3(middle_write, bu", "view3(middle_write, bz")
        .replace("view3(middle_read, bu", "view3(middle_read, bz")
        .replace("view3(repacked_write, bu", "view3(repacked_write, bz")
        .replace("view3(repacked_read, bu", "view3(repacked_read, bz")
        .replace("regroup(t, first_pack);", "regroup(dt, first_pack); release(dt_read);")
        .replace("rebind(t, first_read);", "rebind(dt, first_read);")
        .replace("(ev, t, a, intermediate)", "(ev, dt, a, intermediate)")
        .replace("release(checked);", "release(checked); release(input_d); drop(diagonal); drop(first_result);");
    source
        .lines()
        .map(|line| {
            if !line.trim_start().starts_with("expect(checked,") {
                return line.to_owned();
            }
            let row: usize = line.split(',').nth(1).unwrap().trim().parse().unwrap();
            let factor = if row.is_multiple_of(2) { 2.0 } else { 3.0 };
            let marker = if complex {
                "complex_bits("
            } else {
                "f64_bits("
            };
            let (prefix, tail) = line.split_once(marker).unwrap();
            let inside = tail.split(')').next().unwrap();
            let scaled = inside
                .split(',')
                .map(|word| {
                    let old: u64 = word.trim().parse().unwrap();
                    (f64::from_bits(old) * factor).to_bits().to_string()
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!("{prefix}{marker}{scaled}));")
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn repeated_chain(complex: bool, n: usize) -> String {
    let profile = if complex {
        "ComplexSmooth"
    } else {
        "RealSmooth"
    };
    let scalar = if complex { "Complex<F64>" } else { "F64" };
    let width = if complex { 16 } else { 8 };
    let count = 2 + (n + 1) * n;
    let literal = if complex {
        "complex_bits(0, 4607182418800017408)"
    } else {
        "f64_bits(4607182418800017408)"
    };
    let expected = if complex {
        format!("complex_bits(0, {})", (-((n * n) as f64)).to_bits())
    } else {
        format!("f64_bits({})", ((n * n) as f64).to_bits())
    };
    let mut source = format!("pub resource fn product() -> Unit {{
        space v = linear(super::profiles::{profile}, {n}); basis bv = basis(v);
        space vd = dual(v); basis bvd = derived(bv, vd);
        allocate input: {scalar}[{count}]; allocate scratch: {scalar}[{count}]; allocate result: {scalar}[{count}];
        borrow initial = write(input, layout({width}, {n}, {n}, {}, false)); fill(initial, {literal}); release(initial);
        borrow source = read(input, layout({width}, {n}, {n}, {}, false)); tensor t = view2(source, bv, bvd);
        borrow output = write(result, layout({width}, {n}, {n}, {}, false)); tensor c = view2(output, bv, bvd);
        contract_tree(c, NativeFast) {{
            occurrence a = t; occurrence b = t; occurrence c = t;
            edge ab = (a[1],b[0]); edge bc = (b[1],c[0]); boundary(a[0],c[1]);
            plan {{
                borrow middle_write = write(scratch, layout({width}, {n}, {n}, {}, false)); tensor middle = view2(middle_write, bv, bvd);
                join ab = (ab,a,b,middle); release(middle_write);
                borrow middle_read = read(scratch, layout({width}, {n}, {n}, {}, false)); tensor read_middle = view2(middle_read, bv, bvd); rebind(ab,read_middle);
                join done = (bc,ab,c,c); release(middle_read);
            }}
        }}
        release(output); borrow checked = read(result, layout({width}, {n}, {n}, {}, false));",n+1,n+1,n+1,n+1,n+1,n+1);
    for column in 0..n {
        for row in 0..n {
            source.push_str(&format!("expect(checked,{row},{column},{expected});"));
        }
    }
    source.push_str("release(checked); release(source); drop(result); drop(scratch); drop(input); value { () } }");
    source
}

#[test]
fn immutable_repeated_occurrences_and_empty_rank_two_trees_are_supported() {
    for n in [0, 2, 3] {
        let s = fixture(&repeated_chain(false, n), &repeated_chain(true, n));
        success(&command(&s, "check").output().unwrap());
        let emission = kernel(captured(&s), "emit");
        assert_eq!(emission["ok"], true, "{emission}");
        let code = emission["lean_source"].as_str().unwrap();
        assert_eq!(code.matches("allocate arena").count(), 6);
        assert_eq!(code.matches("VastitasGemmNative.gemm arena").count(), 4);
        assert!(!code.contains("pack3 arena") && !code.contains("regroup3 arena"));
    }
}

#[test]
fn unused_tree_bodies_are_audited_without_linking_the_numerical_runtime() {
    let s = fixture(REAL, COMPLEX);
    s.write(
        "src/main.vast",
        "mod profiles; mod real; mod complex; fn main() -> Int { 42 }",
    );
    let emitted = kernel(captured(&s), "emit");
    assert_eq!(emitted["ok"], true, "{emitted}");
    assert_eq!(emitted["numerical_runtime"], false);
    success(
        &command(&s, "build")
            .args(["-o", "ordinary"])
            .output()
            .unwrap(),
    );
    let run = Command::new(s.0.join("ordinary")).output().unwrap();
    success(&run);
    assert_eq!(run.stdout, b"42\n");
    s.write(
        "src/real/mod.vast",
        &REAL.replace("(ew, ta, b, c)", "(ev, ta, b, c)"),
    );
    assert!(!command(&s, "check").output().unwrap().status.success());
}

fn oriented_pair(
    complex: bool,
    tensor_axis: usize,
    matrix_axis: usize,
    tensor_left: bool,
    dims: [usize; 3],
) -> String {
    let profile = if complex {
        "ComplexSmooth"
    } else {
        "RealSmooth"
    };
    let scalar = if complex { "Complex<F64>" } else { "F64" };
    let width = if complex { 16 } else { 8 };
    let literal = |(re, im): (f64, f64)| {
        if complex {
            format!("complex_bits({}, {})", re.to_bits(), im.to_bits())
        } else {
            format!("f64_bits({})", re.to_bits())
        }
    };
    let tensor_fill = (1.0, if complex { 1.0 } else { 0.0 });
    let tensor_patch = (3.0, if complex { 2.0 } else { 0.0 });
    let matrix_fill = (2.0, if complex { -1.0 } else { 0.0 });
    let matrix_patch = (-1.0, if complex { 3.0 } else { 0.0 });
    let bases = ["bu", "bv", "bw"];
    let free: Vec<_> = (0..3).filter(|axis| *axis != tensor_axis).collect();
    let t_order = if tensor_left {
        vec![free[0], free[1], tensor_axis]
    } else {
        vec![tensor_axis, free[0], free[1]]
    };
    let t_split = if tensor_left { 2 } else { 1 };
    let m_order = if tensor_left {
        vec![matrix_axis, 1 - matrix_axis]
    } else {
        vec![1 - matrix_axis, matrix_axis]
    };
    let m_axes = if matrix_axis == 0 {
        vec!["bd", "bf"]
    } else {
        vec!["bf", "bd"]
    };
    let m_dims = if matrix_axis == 0 {
        vec![dims[tensor_axis], 5]
    } else {
        vec![5, dims[tensor_axis]]
    };
    let output_axes = if tensor_left {
        vec![bases[free[0]], bases[free[1]], "bf"]
    } else {
        vec!["bf", bases[free[0]], bases[free[1]]]
    };
    let output_dims = if tensor_left {
        vec![dims[free[0]], dims[free[1]], 5]
    } else {
        vec![5, dims[free[0]], dims[free[1]]]
    };
    let output_split = if tensor_left { 2 } else { 1 };
    let t_shape = (
        t_order[..t_split]
            .iter()
            .map(|a| dims[*a])
            .product::<usize>(),
        t_order[t_split..]
            .iter()
            .map(|a| dims[*a])
            .product::<usize>(),
    );
    let m_shape = (m_dims[m_order[0]], m_dims[m_order[1]]);
    let output_shape = (
        output_dims[..output_split].iter().product::<usize>(),
        output_dims[output_split..].iter().product::<usize>(),
    );
    let mut source = format!(
        "pub resource fn product() -> Unit {{
        space u = linear(super::profiles::{profile}, {}); basis bu = basis(u);
        space v = linear(super::profiles::{profile}, {}); basis bv = basis(v);
        space w = linear(super::profiles::{profile}, {}); basis bw = basis(w);
        space f = linear(super::profiles::{profile}, 5); basis bf = basis(f);
        space d = dual({}); basis bd = derived({},d);",
        dims[0],
        dims[1],
        dims[2],
        ["u", "v", "w"][tensor_axis],
        bases[tensor_axis]
    );
    let layout = |(r, c): (usize, usize)| format!("layout({width},{r},{c},{},false)", r + 1);
    for (owner, shape) in [
        ("original", (dims[0], dims[1] * dims[2])),
        ("matrix", (m_dims[0], m_dims[1])),
        ("ts", t_shape),
        ("ms", m_shape),
        ("result", output_shape),
    ] {
        source.push_str(&format!(
            "allocate {owner}: {scalar}[{}];",
            2 + (shape.0 + 1) * shape.1
        ));
    }
    source.push_str(&format!(
        "borrow init_t = write(original,{}); fill(init_t,{});",
        layout((dims[0], dims[1] * dims[2])),
        literal(tensor_fill)
    ));
    if dims.iter().all(|n| *n > 1) {
        source.push_str(&format!(
            "store(init_t,1,{},{});",
            1 + dims[1],
            literal(tensor_patch)
        ));
    }
    source.push_str(&format!(
        "release(init_t); borrow init_m = write(matrix,{}); fill(init_m,{});",
        layout((m_dims[0], m_dims[1])),
        literal(matrix_fill)
    ));
    if dims[tensor_axis] > 0 {
        source.push_str(&format!(
            "store(init_m,{},{},{});",
            if matrix_axis == 0 { 0 } else { 4 },
            if matrix_axis == 0 { 4 } else { 0 },
            literal(matrix_patch)
        ));
    }
    source.push_str(&format!("release(init_m);
        borrow input_t = read(original,{}); tensor t = view3(input_t,bu,bv,bw,axes(0,1,2),1);
        borrow input_m = read(matrix,{}); tensor m = view2(input_m,{},{});
        borrow output = write(result,{}); tensor c = view3(output,{},{},{},axes(0,1,2),{output_split});
        contract_tree(c,NativeFast) {{ occurrence t=t; occurrence m=m;
            edge edge = (m[{matrix_axis}],t[{tensor_axis}]); boundary({}); plan {{
            borrow tw = write(ts,{}); tensor tp = view3(tw,bu,bv,bw,axes({},{},{}),{t_split});
            regroup(t,tp); release(tw); borrow tr = read(ts,{}); tensor ti = view3(tr,bu,bv,bw,axes({},{},{}),{t_split}); rebind(t,ti);
            borrow mw = write(ms,{}); tensor mp = view2(mw,{},{},axes({},{}),1);
            regroup(m,mp); release(mw); borrow mr = read(ms,{}); tensor mi = view2(mr,{},{},axes({},{}),1); rebind(m,mi);
            join done = (edge,{},{},c); release(mr); release(tr); }} }}
        release(output); borrow checked = read(result,{});",
        layout((dims[0],dims[1]*dims[2])),layout((m_dims[0],m_dims[1])),m_axes[0],m_axes[1],layout(output_shape),output_axes[0],output_axes[1],output_axes[2],
        if tensor_left {format!("t[{}],t[{}],m[{}]",free[0],free[1],1-matrix_axis)} else {format!("m[{}],t[{}],t[{}]",1-matrix_axis,free[0],free[1])},
        layout(t_shape),t_order[0],t_order[1],t_order[2],layout(t_shape),t_order[0],t_order[1],t_order[2],
        layout(m_shape),m_axes[0],m_axes[1],m_order[0],m_order[1],layout(m_shape),m_axes[0],m_axes[1],m_order[0],m_order[1],
        if tensor_left {"t"}else{"m"},if tensor_left {"m"}else{"t"},layout(output_shape)));
    for column in 0..output_shape.1 {
        for row in 0..output_shape.0 {
            let mut coords = [0; 3];
            let mut rr = row;
            let mut cc = column;
            for axis in 0..output_split {
                coords[axis] = rr % output_dims[axis];
                rr /= output_dims[axis];
            }
            for axis in output_split..3 {
                coords[axis] = cc % output_dims[axis];
                cc /= output_dims[axis];
            }
            let (free0, free1, f) = if tensor_left {
                (coords[0], coords[1], coords[2])
            } else {
                (coords[1], coords[2], coords[0])
            };
            let mut expected = (0.0, 0.0);
            for k in 0..dims[tensor_axis] {
                let mut logical = [0; 3];
                logical[tensor_axis] = k;
                logical[free[0]] = free0;
                logical[free[1]] = free1;
                let t = if logical == [1, 1, 1] && dims.iter().all(|n| *n > 1) {
                    tensor_patch
                } else {
                    tensor_fill
                };
                let m = if k == 0 && f == 4 {
                    matrix_patch
                } else {
                    matrix_fill
                };
                let (l, r) = if tensor_left { (t, m) } else { (m, t) };
                expected.0 += l.0 * r.0 - l.1 * r.1;
                expected.1 += l.0 * r.1 + l.1 * r.0;
            }
            source.push_str(&format!(
                "expect(checked,{row},{column},{});",
                literal(expected)
            ));
        }
    }
    source.push_str("release(checked); release(input_m); release(input_t); drop(result); drop(ms); drop(ts); drop(matrix); drop(original); value { () } }");
    source
}

#[test]
fn explicit_regroup_supports_every_rank_two_three_selected_axis_orientation() {
    for tensor_axis in 0..3 {
        for matrix_axis in 0..2 {
            for tensor_left in [false, true] {
                let s = fixture(
                    &oriented_pair(false, tensor_axis, matrix_axis, tensor_left, [2, 3, 4]),
                    &oriented_pair(true, tensor_axis, matrix_axis, tensor_left, [2, 3, 4]),
                );
                success(&command(&s, "check").output().unwrap());
            }
        }
    }
}

fn with_cache(source: &str, complex: bool, condition: bool, overwrite: bool) -> String {
    let width = if complex { 16 } else { 8 };
    let scalar = if complex { "Complex<F64>" } else { "F64" };
    let source = source.replace(
        "    contract_tree(c, NativeFast) {",
        &format!(
            "allocate cache_buffer: {scalar}[48]; allocate cache_result: {scalar}[48];
        borrow cache_write = write(cache_buffer,layout({width},8,3,9,false));
        tensor cache_destination = view3(cache_write,bu,bvd,bwd,axes(0,2,1),2);
        cache saved = pack3(t,cache_destination); release(cache_write);
    contract_tree(c, NativeFast) {{"
        ),
    );
    let source = if overwrite {
        source
            .replace(
                &format!("write(scratch, layout({width}, 10, 4, 11, false))"),
                &format!("write(cache_buffer, layout({width}, 10, 4, 11, false))"),
            )
            .replace(
                &format!("read(scratch, layout({width}, 10, 4, 11, false))"),
                &format!("read(cache_buffer, layout({width}, 10, 4, 11, false))"),
            )
    } else {
        source
    };
    let mut consume=format!("borrow cache_read = read(cache_buffer,layout({width},8,3,9,false));
        tensor cache_input = view3(cache_read,bu,bvd,bwd,axes(0,2,1),2);
        borrow cache_output = write(cache_result,layout({width},8,5,9,false));
        tensor cache_c = view3(cache_output,bu,bwd,bad,axes(0,1,2),2);
        contract3_cached(saved,cache_input,right_a,cache_c,NativeFast); release(cache_output); release(cache_read);
        borrow check_cache = read(cache_result,layout({width},8,5,9,false));");
    for a in 0..5 {
        for w in 0..4 {
            for u in 0..2 {
                let mut expected: (f64, f64) = (0.0, 0.0);
                for v in 0..3 {
                    let t = if u == 1 && v == 1 && w == 0 {
                        (3.0, if complex { 2.0 } else { 0.0 })
                    } else {
                        (1.0, if complex { 1.0 } else { 0.0 })
                    };
                    let m = if v == 0 && a == 4 {
                        (2.0, if complex { -1.0 } else { 0.0 })
                    } else {
                        (1.0, if complex { 1.0 } else { 0.0 })
                    };
                    expected.0 += t.0 * m.0 - t.1 * m.1;
                    expected.1 += t.0 * m.1 + t.1 * m.0;
                }
                let literal = if complex {
                    format!(
                        "complex_bits({},{})",
                        expected.0.to_bits(),
                        expected.1.to_bits()
                    )
                } else {
                    format!("f64_bits({})", expected.0.to_bits())
                };
                consume.push_str(&format!("expect(check_cache,{},{a},{literal});", u + 2 * w));
            }
        }
    }
    consume.push_str("release(check_cache); drop(cache_result); drop(cache_buffer);");
    let source = source.replace(
        "    release(output);",
        &format!("{consume}\n    release(output);"),
    );
    let header = "pub resource fn product() -> Unit {";
    let body = source.strip_prefix(header).unwrap();
    let (body, _) = body.rsplit_once("    value { () }").unwrap();
    format!("{header} if {condition} {{ {body} }} else {{ {body} }} value {{ () }} }}")
}

#[test]
fn trees_preserve_unrelated_cache_and_invalidate_generic_regroup_destinations() {
    for condition in [false, true] {
        let real = with_cache(REAL, false, condition, false);
        let complex = with_cache(COMPLEX, true, condition, false);
        let s = fixture(&real, &complex);
        success(&command(&s, "check").output().unwrap());
        let emission = kernel(captured(&s), "emit");
        assert_eq!(emission["ok"], true, "{emission}");
        let code = emission["lean_source"].as_str().unwrap();
        assert_eq!(code.matches("pack3 arena").count(), 8);
        assert_eq!(code.matches("regroup3 arena").count(), 4);
        assert_eq!(code.matches("VastitasGemmNative.gemm arena").count(), 12);
        assert_eq!(code.matches("allocate arena").count(), 32);
        assert!(!code.contains("requireDependency") && !code.contains("captureDependency"));
        rejection(&with_cache(REAL, false, condition, true), "E_TENSOR");
    }
}

fn long_chain(count: usize) -> String {
    let mut source=String::from("pub resource fn product() -> Unit {
        space v = linear(super::profiles::RealSmooth,1); basis bv = basis(v);
        space vd = dual(v); basis bvd = derived(bv,vd);
        allocate input: F64[1]; allocate s0: F64[1]; allocate s1: F64[1]; allocate result: F64[1];
        borrow init = write(input,layout(0,1,1,1,false)); fill(init,f64_bits(4607182418800017408)); release(init);
        borrow input_read = read(input,layout(0,1,1,1,false)); tensor t = view2(input_read,bv,bvd);
        borrow output = write(result,layout(0,1,1,1,false)); tensor c = view2(output,bv,bvd);
        contract_tree(c,NativeFast) {");
    for index in 0..count {
        source.push_str(&format!("occurrence n{index}=t;"));
    }
    for index in 0..count - 1 {
        source.push_str(&format!("edge e{index}=(n{index}[1],n{}[0]);", index + 1));
    }
    source.push_str(&format!("boundary(n0[0],n{}[1]); plan {{", count - 1));
    for index in 0..count - 1 {
        let last = index == count - 2;
        let target = if last {
            "c".to_owned()
        } else {
            format!("o{index}")
        };
        let left = if index == 0 {
            "n0".to_owned()
        } else {
            format!("p{}", index - 1)
        };
        if !last {
            source.push_str(&format!("borrow w{index}=write(s{},layout(0,1,1,1,false)); tensor o{index}=view2(w{index},bv,bvd);",index%2));
        }
        source.push_str(&format!(
            "join p{index}=(e{index},{left},n{},{target});",
            index + 1
        ));
        if index > 0 {
            source.push_str(&format!("release(r{});", index - 1));
        }
        if !last {
            source.push_str(&format!("release(w{index}); borrow r{index}=read(s{},layout(0,1,1,1,false)); tensor v{index}=view2(r{index},bv,bvd); rebind(p{index},v{index});",index%2));
        }
    }
    source.push_str("} } release(output); borrow checked=read(result,layout(0,1,1,1,false)); expect(checked,0,0,f64_bits(4607182418800017408)); release(checked); release(input_read); drop(result); drop(s1); drop(s0); drop(input); value { () } }");
    source
}

#[test]
fn finite_tree_bound_accepts_all_sixty_four_nodes_and_rejects_sixty_five() {
    let s = fixture(&long_chain(64), COMPLEX);
    success(&command(&s, "check").output().unwrap());
    rejection(&long_chain(65), "E_TENSOR_TREE");
}

#[test]
fn explicit_trees_preserve_order_reuse_scratch_and_audit_both_branches() {
    for (real, complex, count) in [
        (REAL.to_owned(), COMPLEX.to_owned(), 4),
        (
            four_occurrences(REAL, false),
            four_occurrences(COMPLEX, true),
            6,
        ),
        (branched(REAL, false), branched(COMPLEX, false), 8),
        (branched(REAL, true), branched(COMPLEX, true), 8),
    ] {
        let s = fixture(&real, &complex);
        success(&command(&s, "check").output().unwrap());
        let emitted = kernel(captured(&s), "emit");
        assert_eq!(emitted["ok"], true, "{emitted}");
        let code = emitted["lean_source"].as_str().unwrap();
        assert_eq!(code.matches("VastitasGemmNative.gemm arena").count(), count);
        let branch_factor = if count == 8 { 2 } else { 1 };
        assert_eq!(code.matches("pack3 arena").count(), 2 * branch_factor);
        assert_eq!(code.matches("regroup3 arena").count(), 2 * branch_factor);
        assert_eq!(
            code.matches("allocate arena").count(),
            if count == 6 { 16 } else { 12 }
        );
        assert!(!code.contains("copy arena"));
    }
    let reordered = REAL
        .replace(
            "occurrence t = t; occurrence a = right_a; occurrence b = right_b;",
            "occurrence b = right_b; occurrence t = t; occurrence a = right_a;",
        )
        .replace(
            "edge ev = (t[1], a[0]); edge ew = (t[2], b[0]);",
            "edge ew = (t[2], b[0]); edge ev = (t[1], a[0]);",
        );
    let original = kernel(captured(&fixture(REAL, COMPLEX)), "emit");
    let reordered = kernel(captured(&fixture(&reordered, COMPLEX)), "emit");
    assert_eq!(original["lean_source"], reordered["lean_source"]);
}

#[test]
fn trees_reject_wrong_ports_nominal_axes_and_forged_producers() {
    for (from, to) in [
        ("t[1], a[0]", "t[1], a[1]"),
        ("t[2], b[0]", "t[1], b[0]"),
        ("t[1], a[0]", "unknown[1], a[0]"),
        ("boundary(t[0], a[1], b[1])", "boundary(a[1], t[0], b[1])"),
        ("(ew, ta, b, c)", "(ev, ta, b, c)"),
        ("(ev, t, a, intermediate)", "(ev, a, t, intermediate)"),
        ("(ev, t, a, intermediate)", "(ev, t, t, intermediate)"),
        ("join ta =", "join t ="),
        ("rebind(t, first_read);", ""),
        ("release(packed_write);", ""),
        ("release(repacked_read);", ""),
    ] {
        rejection(
            &REAL.replace(from, to),
            if from == "release(packed_write);" {
                "E_RESOURCE_ALIAS"
            } else {
                "E_TENSOR"
            },
        );
    }
    rejection(&REAL.replace("basis bv = basis(v);", "basis bv = basis(v); space alien = linear(super::profiles::RealSmooth, 3); basis alien_basis = basis(alien);")
        .replace("view2(input_a, bv, bad)", "view2(input_a, alien_basis, bad)"), "E_TENSOR_TREE");
    rejection(
        &REAL.replace(
            "space vd = dual(v)",
            "involution sigma = canonical(v); space vd = conjugate(v, sigma)",
        ),
        "E_TENSOR_TREE",
    );
    // Rebinding cannot relabel an unrelated initialized allocation of equal shape.
    rejection(&REAL.replace("allocate scratch: F64[47];", "allocate scratch: F64[47]; allocate fake: F64[47]; borrow fake_write = write(fake, layout(8, 8, 3, 9, false)); fill(fake_write, f64_bits(0)); release(fake_write);")
        .replace("read(scratch, layout(8, 8, 3, 9, false))", "read(fake, layout(8, 8, 3, 9, false))")
        .replace("drop(result);", "drop(fake); drop(result);"), "E_TENSOR_TREE");
    let opaque = REAL.replace("    contract_tree(c, NativeFast) {", "    call hide(v,bv) -> (opaque);\n    contract_tree(c, NativeFast) {")
        .replace("        plan {", "        plan { borrow illicit = read(opaque, layout(0,2,3,2,false)); release(illicit);");
    rejection(&format!("{opaque}\nresource fn hide(v: Space<super::profiles::RealSmooth,3>, bv: Basis<v>) returns (boxed: OwnedMapTo<bv,2>) -> Unit {{
        space hidden = linear(super::profiles::RealSmooth,2); basis hidden_basis = basis(hidden);
        allocate buffer: F64[6]; borrow init = write(buffer,layout(0,2,3,2,false)); fill(init,f64_bits(0)); release(init);
        map matrix = owned(buffer,layout(0,2,3,2,false),bv,hidden_basis); map boxed = pack(matrix); value {{ () }}
    }}"), "E_TENSOR_TREE");
    // Invalid dead arms and uncalled bodies are still audited.
    rejection(
        &branched(REAL, false).replacen("(ew, ta, b, c)", "(ev, ta, b, c)", 1),
        "E_TENSOR",
    );
    rejection(
        &format!(
            "{REAL}\n{}",
            REAL.replace("pub resource fn product()", "resource fn unused()")
                .replace("(ew, ta, b, c)", "(ev, ta, b, c)")
        ),
        "E_TENSOR",
    );
}

#[test]
fn raw_tree_protocol_rechecks_bounded_graph_and_plan_authority() {
    let original = captured(&fixture(REAL, COMPLEX));
    for version in 2..8 {
        let mut changed = original.clone();
        changed["version"] = json!(version);
        wire_rejected(changed);
    }
    for extra in ["checked", "proof", "allocation", "flags"] {
        let mut raw = original.clone();
        tree(&mut raw)[extra] = json!(true);
        wire_rejected(raw);
    }
    let real_body = original["packages"][0]["modules"]
        .as_array()
        .unwrap()
        .iter()
        .find(|module| module["path"] == json!(["real"]))
        .unwrap()["resource_functions"][0]["body"]
        .as_array()
        .unwrap();
    let mut fill = real_body
        .iter()
        .find(|statement| statement["action"]["op"] == "fill")
        .unwrap()["action"]
        .clone();
    fill["loan"] = json!("output");
    for action in [
        fill,
        json!({"op":"drop","owner":"original"}),
        json!({"op":"copy","source":"input_t","target":"output"}),
    ] {
        let mut raw = original.clone();
        tree(&mut raw)["plan"]
            .as_array_mut()
            .unwrap()
            .insert(0, json!({"kind":"action","action":action}));
        let response = kernel(raw, "emit");
        assert_eq!(response["ok"], false, "{response}");
        assert_eq!(
            response["diagnostics"][0]["code"], "E_TENSOR_TREE",
            "{response}"
        );
        assert!(response.get("lean_source").is_none());
    }
    for field in ["occurrences", "edges", "boundary"] {
        let mut raw = original.clone();
        tree(&mut raw)["graph"][field] = json!([]);
        wire_rejected(raw);
    }
    let mut raw = original.clone();
    let step = tree(&mut raw)["plan"][0].clone();
    tree(&mut raw)["plan"] = json!(vec![step; 1025]);
    wire_rejected(raw);
    let mut raw = original.clone();
    tree(&mut raw)["graph"]["edges"][0]["dual"]["axis"] = json!(3);
    wire_rejected(raw);
    let mut raw = original.clone();
    tree(&mut raw)["plan"][2]["component"] = json!("forged");
    wire_rejected(raw);
}

#[test]
#[ignore = "requires explicit pinned OpenBLAS prefix; numerical CI runs this test"]
fn tree_native_executes_multiedge_branching_and_written_operand_order() {
    let prefix =
        std::env::var_os("VASTITAS_TEST_OPENBLAS_PREFIX").expect("explicit numerical prefix");
    let mut cases = vec![
        (REAL.to_owned(), COMPLEX.to_owned()),
        (
            four_occurrences(REAL, false),
            four_occurrences(COMPLEX, true),
        ),
        (branched(REAL, false), branched(COMPLEX, false)),
        (branched(REAL, true), branched(COMPLEX, true)),
        (repeated_chain(false, 0), repeated_chain(true, 0)),
        (repeated_chain(false, 2), repeated_chain(true, 2)),
        (repeated_chain(false, 3), repeated_chain(true, 3)),
    ];
    for tensor_axis in 0..3 {
        for matrix_axis in 0..2 {
            for tensor_left in [false, true] {
                cases.push((
                    oriented_pair(false, tensor_axis, matrix_axis, tensor_left, [2, 3, 4]),
                    oriented_pair(true, tensor_axis, matrix_axis, tensor_left, [2, 3, 4]),
                ));
            }
        }
    }
    for dims in [[0, 3, 4], [2, 0, 4], [2, 3, 0]] {
        cases.push((
            oriented_pair(false, 1, 0, true, dims),
            oriented_pair(true, 1, 0, true, dims),
        ));
    }
    for condition in [false, true] {
        cases.push((
            with_cache(REAL, false, condition, false),
            with_cache(COMPLEX, true, condition, false),
        ));
    }
    for (real, complex) in cases {
        let s = fixture(&real, &complex);
        success(&command(&s, "check").output().unwrap());
        let mut build = command(&s, "build");
        build
            .args(["-o", "program", "--openblas-prefix"])
            .arg(&prefix);
        if let Some(cc) = std::env::var_os("VASTITAS_TEST_NATIVE_CC") {
            build.arg("--native-cc").arg(cc);
        }
        success(&build.output().unwrap());
        let result = Command::new(s.0.join("program")).output().unwrap();
        success(&result);
        assert_eq!(result.stdout, b"42\n");
    }
}
