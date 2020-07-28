const defaultValue = `-- Live ${
  (self as any).WebAssembly ? 'WebAssembly' : 'JavaScript'
} version of Lean
#eval let v := lean.version in let s := lean.special_version_desc in string.join
["Lean (version ", v.1.repr, ".", v.2.1.repr, ".", v.2.2.repr, ", ",
if s ≠ "" then s ++ ", " else s, "commit ", (lean.githash.to_list.take 12).as_string, ")"]

example (m n : ℕ) : m + n = n + m :=
by simp [nat.add_comm]`;

export interface HashParams {
  url: string;
  code: string;
}

export function parseHash(hash: string): HashParams {
  hash = hash.slice(1);
  const hashObj = hash
    .split('&')
    .map((s) => s.split('='))
    .reduce((pre, [key, value]) => ({ ...pre, [key]: value }), {}) as any;
  const url = decodeURIComponent(hashObj.url || '');
  const code = decodeURIComponent(hashObj.code || defaultValue);

  return { url, code };
}

export function paramsToString(params: HashParams): string {
  let s = '#';

  if (params.url) {
    s =
      '#url=' +
      encodeURIComponent(params.url)
        .replace(/\(/g, '%28')
        .replace(/\)/g, '%29');
  }

  // nonempty params.code will wipe out params.url
  if (params.code) {
    params.url = null;
    s =
      '#code=' +
      encodeURIComponent(params.code)
        .replace(/\(/g, '%28')
        .replace(/\)/g, '%29');
  }

  return s;
}
