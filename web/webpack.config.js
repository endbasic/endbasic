const path = require("path");
const CopyWebpackPlugin = require("copy-webpack-plugin");
const WasmPackPlugin = require("@wasm-tool/wasm-pack-plugin");

const distDir = path.resolve(__dirname, "dist");

module.exports = {
    mode: "production",
    entry: {
        index: "./js/bootstrap.js",
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
        contentBase: distDir,
    },
    plugins: [
        new CopyWebpackPlugin({
            patterns: [
                path.resolve(__dirname, "static"),
                {
                    from: path.resolve(__dirname, "node_modules/xterm/css/xterm.css"),
                    to: "xterm.css",
                },
            ],
        }),

        new WasmPackPlugin({
            crateDirectory: path.resolve(__dirname),
        }),
    ],
};
