'use strict';
/*!
 * Copyright (c) Microsoft Corporation. All rights reserved.
 */
var __importDefault =
  (this && this.__importDefault) ||
  function (mod) {
    return mod && mod.__esModule ? mod : { default: mod };
  };
Object.defineProperty(exports, '__esModule', { value: true });
const fs_1 = __importDefault(require('fs'));
const path_1 = __importDefault(require('path'));
const moniker_1 = __importDefault(require('moniker'));
const nconf_1 = __importDefault(require('nconf'));
const odsp_utils_1 = require('@fluidframework/odsp-utils');
const tool_utils_1 = require('@fluidframework/tool-utils');
const axios_1 = __importDefault(require('axios'));
const bohemiaIntercept_1 = require('./bohemiaIntercept');
const multiResolver_1 = require('./multiResolver');
const tokenManager = new tool_utils_1.OdspTokenManager(
  tool_utils_1.odspTokensCache,
);
let odspAuthStage = 0;
let odspAuthLock;
const getThisOrigin = (options) => `http://localhost:${options.port}`;
exports.before = async (app) => {
  app.get('/getclientsidewebparts', async (req, res) =>
    res.send(await bohemiaIntercept_1.createManifestResponse()),
  );
  app.get('/', (req, res) => res.redirect(`/${moniker_1.default.choose()}`));
};
exports.after = (app, server, baseDir, env, paths, styles, scripts) => {
  console.log(paths, styles, scripts);

  const options = Object.assign(Object.assign({ mode: 'local' }, env), {
    port: server.options.port,
  });
  const config = nconf_1.default
    .env('__')
    .file(path_1.default.join(baseDir, 'config.json'));
  // Check that tinylicious is running when it is selected
  switch (options.mode) {
    case 'docker': {
      // Include Docker Check
      break;
    }
    case 'tinylicious': {
      axios_1.default
        .get(multiResolver_1.tinyliciousUrls.hostUrl)
        .then()
        .catch((err) => {
          throw new Error(
            "Tinylicious isn't running. Start the Fluid Framework Tinylicious server",
          );
        });
      break;
    }
    default: {
      break;
    }
  }
  if (
    options.mode === 'docker' ||
    options.mode === 'r11s' ||
    options.mode === 'tinylicious'
  ) {
    options.bearerSecret =
      options.bearerSecret || config.get('fluid:webpack:bearerSecret');
    if (options.mode !== 'tinylicious') {
      options.tenantId =
        options.tenantId || config.get('fluid:webpack:tenantId') || 'fluid';
      if (options.mode === 'docker') {
        options.tenantSecret =
          options.tenantSecret ||
          config.get('fluid:webpack:docker:tenantSecret') ||
          'create-new-tenants-if-going-to-production';
      } else {
        options.tenantSecret =
          options.tenantSecret || config.get('fluid:webpack:tenantSecret');
      }
      if (options.mode === 'r11s') {
        options.fluidHost =
          options.fluidHost || config.get('fluid:webpack:fluidHost');
      }
    }
  }
  options.npm = options.npm || config.get('fluid:webpack:npm');
  console.log(options);
  if (options.mode === 'r11s' && !(options.tenantId && options.tenantSecret)) {
    throw new Error(
      'You must provide a tenantId and tenantSecret to connect to a live routerlicious server',
    );
  }
  let readyP;
  if (options.mode === 'spo-df' || options.mode === 'spo') {
    if (!options.forceReauth && options.odspAccessToken) {
      odspAuthStage = options.pushAccessToken ? 2 : 1;
    }
    readyP = async (req, res) => {
      if (req.url === '/favicon.ico') {
        // ignore these
        return false;
      }
      while (odspAuthLock !== undefined) {
        await odspAuthLock;
      }
      let lockResolver;
      odspAuthLock = new Promise((resolve) => {
        lockResolver = () => {
          resolve();
          odspAuthLock = undefined;
        };
      });
      try {
        const originalUrl = `${getThisOrigin(options)}${req.url}`;
        if (odspAuthStage >= 2) {
          if (!options.odspAccessToken || !options.pushAccessToken) {
            throw Error('Failed to authenticate.');
          }
          return true;
        }
        options.server = odsp_utils_1.getServer(options.mode);
        if (odspAuthStage === 0) {
          await tokenManager.getOdspTokens(
            options.server,
            tool_utils_1.getMicrosoftConfiguration(),
            (url) => res.redirect(url),
            async (tokens) => {
              options.odspAccessToken = tokens.accessToken;
              return originalUrl;
            },
            true,
            options.forceReauth,
          );
          odspAuthStage = 1;
          return false;
        }
        await tokenManager.getPushTokens(
          options.server,
          tool_utils_1.getMicrosoftConfiguration(),
          (url) => res.redirect(url),
          async (tokens) => {
            options.pushAccessToken = tokens.accessToken;
            return originalUrl;
          },
          true,
          options.forceReauth,
        );
        odspAuthStage = 2;
        return false;
      } finally {
        lockResolver();
      }
    };
  }
  app.get('/odspLogin', async (req, res) => {
    if (options.mode !== 'spo-df' && options.mode !== 'spo') {
      res.write('Mode must be spo or spo-df to login to ODSP.');
      res.end();
      return;
    }
    await tokenManager.getOdspTokens(
      options.server,
      tool_utils_1.getMicrosoftConfiguration(),
      (url) => res.redirect(url),
      async (tokens) => {
        options.odspAccessToken = tokens.accessToken;
        return `${getThisOrigin(options)}/pushLogin`;
      },
      true,
      true,
    );
  });
  app.get('/pushLogin', async (req, res) => {
    if (options.mode !== 'spo-df' && options.mode !== 'spo') {
      res.write('Mode must be spo or spo-df to login to Push.');
      res.end();
      return;
    }
    options.pushAccessToken = (
      await tokenManager.getPushTokens(
        options.server,
        tool_utils_1.getMicrosoftConfiguration(),
        (url) => res.redirect(url),
        undefined,
        true,
        true,
      )
    ).accessToken;
  });
  app.get('/file*', (req, res) => {
    console.log('file', req.url);
    const buffer = fs_1.default.readFileSync(req.params[0].substr(1));
    res.end(buffer);
  });
  app.get('/:id*', async (req, res) => {
    console.log('id', req.url);
    if (readyP !== undefined) {
      let canContinue = false;
      try {
        canContinue = await readyP(req, res);
      } catch (error) {
        let toLog = error;
        try {
          toLog = JSON.stringify(error);
        } catch (_a) {}
        console.log(toLog);
      }
      if (!canContinue) {
        if (!res.finished) {
          res.end();
        }
        return;
      }
    }

    if (req.url.indexOf('.') !== -1) {
      const extension = req.url.split('.').slice(-1)[0];

      const contentType =
        extension === 'svg'
          ? 'image/svg+xml'
          : extension === 'css'
          ? 'text/css'
          : extension === 'js'
          ? 'text/javascript'
          : 'text/plain';

      for (let p of paths) {
        try {
          const path = `${p}/${req.url}`;
          const buffer = fs_1.default.readFileSync(path);
          res.setHeader('Content-Type', contentType);
          res.end(buffer);
          console.log(`found at ${path}`);
          console.log(`sending as ${contentType}`);
          return;
        } catch {}
      }

      console.log(`didn't find ${req.url}`);
    }

    fluid(req, res, baseDir, options, styles, scripts);
  });
};
const fluid = (req, res, baseDir, options, styles, scripts) => {
  const documentId = req.params.id;
  // eslint-disable-next-line @typescript-eslint/no-require-imports
  const packageJson = require(path_1.default.join(baseDir, './package.json'));
  const html = `<!DOCTYPE html>
<html style="height: 100%;" lang="en">
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>${documentId}</title>
    ${styles.map((s) => `<link rel='stylesheet' href='${s}' />`).join('\n')}
</head>
<body style="margin: 0; height: 100%;">
    <div id="content" style="min-height: 100%;">
    </div>

    <script src="/node_modules/@fluidframework/webpack-component-loader/dist/fluid-loader.bundle.js"></script>
    ${packageJson.fluid.browser.umd.files.map(
      (file) => `<script src="/${file}"></script>\n`,
    )}
    ${scripts.map((s) => `<script src='${s}'></script>`).join('\n')}
    <script>
        var pkgJson = ${JSON.stringify(packageJson)};
        var options = ${JSON.stringify(options)};
        var fluidStarted = false;
        FluidLoader.start(
            "${documentId}",
            pkgJson,
            window["${packageJson.fluid.browser.umd.library}"],
            options,
            document.getElementById("content"))
        .then(() => fluidStarted = true)
        .catch((error) => console.error(error));
    </script>
</body>
</html>`;
  console.log(html);
  res.setHeader('Content-Type', 'text/html');
  res.end(html);
};
//# sourceMappingURL=routes.js.map
