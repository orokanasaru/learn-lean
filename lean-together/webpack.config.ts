import fluidRoute from '@fluidframework/webpack-component-loader';
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
      stats: 'minimal',
      before: (app) => fluidRoute.before(app),
      after: (app, server) => fluidRoute.after(app, server, __dirname, env),
      watchOptions: {
        ignored: '**/node_modules/**',
      },
    },
    mode: 'development',
    devtool: 'source-map',
  };
};
