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
  const code = decodeURIComponent(hashObj.code || '');

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
