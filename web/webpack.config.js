const path = require("path");
const CopyWebpackPlugin = require("copy-webpack-plugin");
const HtmlWebpackPlugin = require('html-webpack-plugin');
const WasmPackPlugin = require("@wasm-tool/wasm-pack-plugin");

const distDir = path.resolve(__dirname, "dist");

module.exports = {
    mode: "production",
    entry: {
        index: "./src/index.js",
    },
    output: {
        path: distDir,
        filename: "[name].js",
    },
    module: {
        rules: [
            { test: /\.css$/, use: "css-loader" },
        ],
    },
    devServer: {
        client: {
            overlay: {
                errors: true,
                warnings: false,
            }
        },
        host: "0.0.0.0",
        port: 8080,
    },
    resolve: {
        alias: {
            "endbasic_web": path.resolve(__dirname, "pkg/index.js")
        }
    },
    experiments: {
        asyncWebAssembly: true
    },
    performance: {
        assetFilter: (asset) => {
            return !asset.match('module.wasm') && !asset.match('index.js');
        }
    },
    plugins: [
        new CopyWebpackPlugin({
            patterns: [
                path.resolve(__dirname, "static")
            ],
        }),

        new HtmlWebpackPlugin({
            template: 'src/index.html',
        }),

        new WasmPackPlugin({
            crateDirectory: path.resolve(__dirname),
            outDir: path.join(__dirname, "pkg"),
        })
    ],
};
