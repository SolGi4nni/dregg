#!/usr/bin/env node
// Docker image IDs are hashes of engine-version-specific config JSON. Docker
// 29 drops default-valued fields that Docker 27 retains while loading the same
// saved image, changing .Id even when every rootfs layer and runtime-relevant
// setting is identical. This digest normalizes those defaults and binds the
// complete ordered rootfs plus every standardized image Config field.
import crypto from "node:crypto";
import fs from "node:fs";

const objectOrEmpty = (value, label) => {
  if (value == null) return {};
  if (typeof value !== "object" || Array.isArray(value)) throw new Error(`${label} must be an object`);
  return value;
};
const stringArrayOrEmpty = (value, label) => {
  const out = arrayOrEmpty(value, label);
  if (out.some((item) => typeof item !== "string")) throw new Error(`${label} must contain only strings`);
  return out;
};
const arrayOrEmpty = (value, label) => {
  if (value == null) return [];
  if (!Array.isArray(value)) throw new Error(`${label} must be an array`);
  return value;
};
const stringOrEmpty = (value, label) => {
  if (value == null) return "";
  if (typeof value !== "string") throw new Error(`${label} must be a string`);
  return value;
};
const boolOrFalse = (value, label) => {
  if (value == null) return false;
  if (typeof value !== "boolean") throw new Error(`${label} must be boolean`);
  return value;
};
const stable = (value) => {
  if (Array.isArray(value)) return value.map(stable);
  if (value && typeof value === "object") {
    return Object.fromEntries(Object.keys(value).sort().map((key) => [key, stable(value[key])]));
  }
  return value;
};

const allowedConfigKeys = new Set([
  "Hostname", "Domainname", "User", "AttachStdin", "AttachStdout", "AttachStderr", "ExposedPorts",
  "Tty", "OpenStdin", "StdinOnce", "Env", "Cmd", "Healthcheck", "ArgsEscaped", "Image", "Volumes",
  "WorkingDir", "Entrypoint", "NetworkDisabled", "MacAddress", "OnBuild", "Labels", "StopSignal", "Shell",
]);

export const portableImageSha = (image) => {
  if (!image || typeof image !== "object" || Array.isArray(image)) throw new Error("image record must be an object");
  const config = image.Config ?? {};
  if (!config || typeof config !== "object" || Array.isArray(config)) throw new Error("Config must be an object");
  const unknown = Object.keys(config).filter((key) => !allowedConfigKeys.has(key));
  if (unknown.length) throw new Error(`unknown Config keys: ${unknown.sort().join(",")}`);
  const layers = stringArrayOrEmpty(image.RootFS?.Layers, "RootFS.Layers");
  if (image.RootFS?.Type !== "layers" || layers.length === 0 || layers.some((x) => !/^sha256:[0-9a-f]{64}$/.test(x))) {
    throw new Error("malformed ordered rootfs layers");
  }
  const labels = objectOrEmpty(config.Labels, "Config.Labels");
  if (Object.values(labels).some((value) => typeof value !== "string")) throw new Error("Config.Labels values must be strings");
  const portable = stable({
    schema: "pathofangels-portable-image-v1",
    created: stringOrEmpty(image.Created, "Created"),
    author: stringOrEmpty(image.Author, "Author"),
    comment: stringOrEmpty(image.Comment, "Comment"),
    architecture: stringOrEmpty(image.Architecture, "Architecture"),
    os: stringOrEmpty(image.Os, "Os"),
    variant: stringOrEmpty(image.Variant, "Variant"),
    config: {
      Hostname: stringOrEmpty(config.Hostname, "Config.Hostname"),
      Domainname: stringOrEmpty(config.Domainname, "Config.Domainname"),
      User: stringOrEmpty(config.User, "Config.User"),
      AttachStdin: boolOrFalse(config.AttachStdin, "Config.AttachStdin"),
      AttachStdout: boolOrFalse(config.AttachStdout, "Config.AttachStdout"),
      AttachStderr: boolOrFalse(config.AttachStderr, "Config.AttachStderr"),
      ExposedPorts: objectOrEmpty(config.ExposedPorts, "Config.ExposedPorts"),
      Tty: boolOrFalse(config.Tty, "Config.Tty"),
      OpenStdin: boolOrFalse(config.OpenStdin, "Config.OpenStdin"),
      StdinOnce: boolOrFalse(config.StdinOnce, "Config.StdinOnce"),
      Env: stringArrayOrEmpty(config.Env, "Config.Env"),
      Cmd: stringArrayOrEmpty(config.Cmd, "Config.Cmd"),
      Healthcheck: config.Healthcheck == null ? null : stable(objectOrEmpty(config.Healthcheck, "Config.Healthcheck")),
      ArgsEscaped: boolOrFalse(config.ArgsEscaped, "Config.ArgsEscaped"),
      Image: stringOrEmpty(config.Image, "Config.Image"),
      Volumes: objectOrEmpty(config.Volumes, "Config.Volumes"),
      WorkingDir: stringOrEmpty(config.WorkingDir, "Config.WorkingDir"),
      Entrypoint: stringArrayOrEmpty(config.Entrypoint, "Config.Entrypoint"),
      NetworkDisabled: boolOrFalse(config.NetworkDisabled, "Config.NetworkDisabled"),
      MacAddress: stringOrEmpty(config.MacAddress, "Config.MacAddress"),
      OnBuild: stringArrayOrEmpty(config.OnBuild, "Config.OnBuild"),
      Labels: labels,
      StopSignal: stringOrEmpty(config.StopSignal, "Config.StopSignal"),
      Shell: stringArrayOrEmpty(config.Shell, "Config.Shell"),
    },
    rootfs: { type: "layers", layers },
  });
  const hash = crypto.createHash("sha256");
  hash.update("pathofangels/portable-image/v1\0");
  hash.update(JSON.stringify(portable));
  return hash.digest("hex");
};

const fixture = () => ({
  Created: "2026-08-04T00:00:00Z", Architecture: "amd64", Os: "linux",
  Config: { User: "dreggnode", Env: ["A=1"], Cmd: null, Entrypoint: ["/node"], ArgsEscaped: true, Labels: { a: "b" } },
  RootFS: { Type: "layers", Layers: [`sha256:${"1".repeat(64)}`, `sha256:${"2".repeat(64)}`] },
});
if (process.argv[2] === "--selftest") {
  const explicit = fixture();
  Object.assign(explicit.Config, { Hostname: "", Domainname: "", AttachStdin: false, AttachStdout: false, AttachStderr: false, Tty: false, OpenStdin: false, StdinOnce: false, Image: "", Volumes: null, WorkingDir: "", OnBuild: null });
  const compact = fixture();
  if (portableImageSha(explicit) !== portableImageSha(compact)) throw new Error("engine default normalization differs");
  for (const mutate of [
    (x) => x.RootFS.Layers.reverse(),
    (x) => { x.Config.Env[0] = "A=2"; },
    (x) => { x.Config.Cmd = ["serve"]; },
    (x) => { x.Config.Labels.a = "c"; },
  ]) {
    const changed = structuredClone(compact); mutate(changed);
    if (portableImageSha(changed) === portableImageSha(compact)) throw new Error("semantic mutation preserved digest");
  }
  const unknown = structuredClone(compact); unknown.Config.FutureRuntimePower = true;
  try { portableImageSha(unknown); throw new Error("unknown Config key accepted"); } catch (error) {
    if (!String(error).includes("unknown Config keys")) throw error;
  }
  process.stdout.write("portable image identity fixtures PASS\n");
} else {
  const docs = JSON.parse(fs.readFileSync(0, "utf8"));
  if (!Array.isArray(docs) || docs.length !== 1) throw new Error("expected exactly one docker image inspect record");
  process.stdout.write(portableImageSha(docs[0]));
}
