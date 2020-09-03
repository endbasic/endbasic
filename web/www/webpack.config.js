const path = require("path");
const CopyWebpackPlugin = require("copy-webpack-plugin");
const WasmPackPlugin = require("@wasm-tool/wasm-pack-plugin");

const distDir = path.resolve(__dirname, "dist");

module.exports = {
    mode: "production",
    entry: {
        index: "./bootstrap.js",
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
                path.resolve(__dirname, ".nojekyll"),
                path.resolve(__dirname, "bootstrap.js"),
                path.resolve(__dirname, "index.html"),
                path.resolve(__dirname, "index.js"),
                path.resolve(__dirname, "style.css"),
                {
                    from: path.resolve(__dirname, "node_modules/xterm/css/xterm.css"),
                    to: "xterm.css",
                },
            ],
        }),

        new WasmPackPlugin({
            crateDirectory: __dirname,
        }),
    ],
};
