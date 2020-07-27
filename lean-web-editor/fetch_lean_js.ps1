$out_dir = "dist"
mkdir $out_dir

$base_url = "https://bryangingechen.github.io/lean/lean-web-editor"
$lib_name = "library" # change to 'libcore' to download a bundle of the core libraries

"lean_js_js.js", "lean_js_wasm.js", "lean_js_wasm.wasm",
"$lib_name.zip", "$lib_name.info.json", "$lib_name.olean_map.json" |
ForEach-Object { Invoke-WebRequest -Uri $base_url/$_ -OutFile $out_dir/$_ }

