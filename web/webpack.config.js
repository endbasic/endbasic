const path = require("path");
const CopyWebpackPlugin = require("copy-webpack-plugin");
const HtmlWebpackPlugin = require('html-webpack-plugin');
const WasmPackPlugin = require("@wasm-tool/wasm-pack-plugin");
const { DefinePlugin } = require("webpack");

const distDir = path.resolve(__dirname, "dist");

function getServiceUrl() {
    var node_env = process.env.NODE_ENV;
    switch (node_env) {
        case "prod":
            return "'https://service.endbasic.dev/'";
        case "staging":
            return "'https://service-staging.endbasic.dev/'";
        case "local":
            return "'http://localhost:7071/'";
        default:
            throw new Error("Invalid NODE_ENV VALUE: " + node_env);
    }
}

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
        }),

        new DefinePlugin({
            __SERVICE_URL__: getServiceUrl()
        })
    ],
};
