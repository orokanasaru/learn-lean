import * as fluidRoute from '@fluidframework/webpack-component-loader';
import MonacoWebpackPlugin from 'monaco-editor-webpack-plugin';
import { Configuration } from 'webpack';
import path from 'path';
import pkg from './package.json';

const componentName = pkg.name.slice(1);

module.exports = (env) => {
  return {
    entry: {
      main: './src/index.ts',
    },
    resolve: {
      extensions: ['.ts', '.tsx', '.js'],
    },
    module: {
      rules: [
        {
          test: /\.tsx?$/,
          loader: 'ts-loader',
        },
        {
          test: /\.css$/,
          use: ['style-loader', 'css-loader'],
        },
        {
          test: /\.ttf$/,
          use: ['file-loader'],
        },
        {
          test: /webworkerscript\.js$/,
          use: { loader: 'worker-loader' },
        },
      ],
    },
    output: {
      filename: 'main.bundle.js',
      path: path.resolve(__dirname, 'dist'),
      library: 'main',
      // https://github.com/webpack/webpack/issues/5767
      // https://github.com/webpack/webpack/issues/7939
      devtoolNamespace: componentName,
      libraryTarget: 'umd',
    },
    devServer: {
      publicPath: '/dist',
      before: (app) => fluidRoute.before(app),
      after: (app, server) =>
        fluidRoute.after(
          app,
          server,
          __dirname,
          env,
          // @ts-ignore
          [
            'dist',
            'node_modules/lean-web-editor/public',
            'node_modules/lean-web-editor/dist',
            'node_modules/lean-web-editor/node_modules/monaco-editor/min',
            'node_modules/lean-web-editor/node_modules/monaco-editor',
          ],
          ['index.css'],
          ['vs/loader.js'],
        ),
      watchOptions: {
        ignored: '**/node_modules/**',
      },
    },
    mode: 'development',
    devtool: 'source-map',
    plugins: [new MonacoWebpackPlugin()],
  } as Configuration;
};
