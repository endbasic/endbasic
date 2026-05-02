const path = require("path");
const CopyWebpackPlugin = require("copy-webpack-plugin");
const HtmlWebpackPlugin = require('html-webpack-plugin');
const { DefinePlugin } = require("webpack");

const distDir = path.resolve(__dirname, "dist");

function getServiceUrl() {
    var node_env = process.env.NODE_ENV;
    switch (node_env) {
        case "prod":
            return "https://service.endbasic.dev/";
        case "staging":
            return "https://service-staging.endbasic.dev/";
        case "local":
            return "http://localhost:7071/";
        default:
            throw new Error("Invalid NODE_ENV VALUE: " + node_env);
    }
}

function getStringEnvVar(name, fallback) {
    if (process.env[name]) {
        return process.env[name];
    }
    return fallback;
}

function getSourceCodeUrl() {
    return getStringEnvVar("SOURCE_CODE_URL", "https://github.com/endbasic/endbasic");
}

function getLicenseUrl() {
    return getStringEnvVar("LICENSE_URL", "https://www.gnu.org/licenses/agpl-3.0.html");
}

function getIssuesUrl() {
    return getStringEnvVar("ISSUES_URL", "https://github.com/endbasic/endbasic/issues/new");
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

        new DefinePlugin({
            __SERVICE_URL__: JSON.stringify(getServiceUrl()),
            __SOURCE_CODE_URL__: JSON.stringify(getSourceCodeUrl()),
            __LICENSE_URL__: JSON.stringify(getLicenseUrl()),
            __ISSUES_URL__: JSON.stringify(getIssuesUrl())
        })
    ],
};
