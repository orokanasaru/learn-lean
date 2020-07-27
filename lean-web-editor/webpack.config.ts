import CopyWebpackPlugin from 'copy-webpack-plugin';
import HtmlWebpackPlugin from 'html-webpack-plugin';
import MonacoWebpackPlugin from 'monaco-editor-webpack-plugin';
import path from 'path';
import TerserPlugin from 'terser-webpack-plugin-legacy';
import webpack from 'webpack';

const MonacoEditorSrc = path.join(
  __dirname,
  'node_modules',
  'react-monaco-editor',
);

const VSMonacoEditorSrc = path.join(
  __dirname,
  'node_modules',
  'monaco-editor',
  'min',
  'vs',
);

const distDir = path.resolve(__dirname, 'dist');

module.exports = {
  entry: {
    jsx: './src/index.tsx',
    // html: './public/index.html',
    // vendor: ['react', 'react-dom']
  },
  output: {
    filename: 'index.js',
    path: distDir,
    publicPath: './',
  },
  resolve: {
    alias: { 'react-monaco-editor': MonacoEditorSrc },
    extensions: ['.ts', '.tsx', '.js'],
  },
  module: {
    rules: [
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
      {
        loader: [
          // To use babel in lean-client-js-browser, add the following to this package.json
          // "babel-core": "^6.26.3",
          // "babel-loader": "^7.1.2",
          // "babel-polyfill": "^6.26.0",
          // "babel-preset-env": "^1.7.0",
          // 'babel-loader?presets[]=env',
          'ts-loader',
        ],
        test: /\.tsx?$/,
      },
    ],
  },
  devServer: {
    contentBase: distDir,
    publicPath: '/',
  },
  plugins: [
    // used to change hostPrefix in index.tsx to 'https://tqft.net/lean/web-editor/'
    new webpack.EnvironmentPlugin({
      COMMUNITY: false,
    }),
    new HtmlWebpackPlugin({
      template: 'public/index.html',
    }),
    new CopyWebpackPlugin({
      patterns: [
        { from: VSMonacoEditorSrc, to: 'vs' },
        { from: 'public/index.css', to: 'index.css' },
        { from: 'public/lean_logo.svg', to: 'lean_logo.svg' },
        { from: 'public/display-goal-light.svg', to: 'display-goal-light.svg' },
        { from: 'public/display-list-light.svg', to: 'display-list-light.svg' },
      ],
    }),
    new TerserPlugin(),
    new MonacoWebpackPlugin(),
  ],
  node: {
    child_process: 'empty',
    readline: 'empty',
  },
  externals: {
    // react: 'require("react")',
    // 'react-dom': 'require("react-dom")',
  },
};
